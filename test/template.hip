#include <hip/hip_runtime.h>
#include <fstream>
#include <vector>
#include <chrono>
#include <iomanip>
#include <cstdlib>

#define HIP_CHECK(call) \
    do { \
        hipError_t err = call; \
        if (err != hipSuccess) { \
            std::cerr << "HIP error at " << __FILE__ << ":" << __LINE__ << " - " << hipGetErrorString(err) << std::endl; \
            exit(1); \
        } \
    } while(0)

__global__ void kernel_version_1(double* input, double* output, size_t n) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        output[idx] = input[idx] * 2.0;
    }
}

__global__ void kernel_version_2(double* input, double* output, size_t n) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        output[idx] = input[idx] * input[idx];
    }
}

class GPUTimer {
private:
    hipEvent_t start_event, stop_event;
    
public:
    GPUTimer() {
        HIP_CHECK(hipEventCreate(&start_event));
        HIP_CHECK(hipEventCreate(&stop_event));
    }
    
    ~GPUTimer() {
        hipEventDestroy(start_event);
        hipEventDestroy(stop_event);
    }
    
    void start() {
        HIP_CHECK(hipEventRecord(start_event));
    }
    
    double stop() {
        HIP_CHECK(hipEventRecord(stop_event));
        HIP_CHECK(hipEventSynchronize(stop_event));
        
        float elapsed_ms;
        HIP_CHECK(hipEventElapsedTime(&elapsed_ms, start_event, stop_event));
        return static_cast<double>(elapsed_ms);
    }
};

void warmup_gpu(double* d_input, double* d_output, size_t n, dim3 grid, dim3 block) {
    for (int i = 0; i < 5; i++) {
        hipLaunchKernelGGL(kernel_version_1, grid, block, 0, 0, d_input, d_output, n);
        HIP_CHECK(hipDeviceSynchronize());
    }
}

double benchmark_kernel(void(*kernel)(double*, double*, size_t), 
                       double* d_input, double* d_output, size_t n, 
                       dim3 grid, dim3 block, int iterations) {
    GPUTimer timer;
    double total_time = 0.0;
    
    for (int i = 0; i < iterations; i++) {
        timer.start();
        hipLaunchKernelGGL(kernel, grid, block, 0, 0, d_input, d_output, n);
        total_time += timer.stop();
    }
    
    return total_time / iterations;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        std::ofstream err_file("benchmark_error.log", std::ios::app);
        err_file << "Usage: " << argv[0] << " <output_file> [array_size] [iterations]" << std::endl;
        return 1;
    }
    
    const char* output_filename = argv[1];
    const size_t n = (argc > 2) ? std::stoull(argv[2]) : 1024 * 1024 * 16;
    const int iterations = (argc > 3) ? std::stoi(argv[3]) : 100;
    const size_t bytes = n * sizeof(double);
    
    hipDeviceProp_t prop;
    HIP_CHECK(hipGetDeviceProperties(&prop, 0));
    
    std::vector<double> h_input(n);
    std::vector<double> h_output(n);
    
    for (size_t i = 0; i < n; i++) {
        h_input[i] = static_cast<double>(i % 1000) + 0.5;
    }
    
    double *d_input, *d_output;
    HIP_CHECK(hipMalloc(&d_input, bytes));
    HIP_CHECK(hipMalloc(&d_output, bytes));
    HIP_CHECK(hipMemcpy(d_input, h_input.data(), bytes, hipMemcpyHostToDevice));
    
    const int block_size = 256;
    dim3 block(block_size);
    dim3 grid((n + block_size - 1) / block_size);
    
    warmup_gpu(d_input, d_output, n, grid, block);
    
    double time_v1 = benchmark_kernel(kernel_version_1, d_input, d_output, n, grid, block, iterations);
    double time_v2 = benchmark_kernel(kernel_version_2, d_input, d_output, n, grid, block, iterations);
    
    double bandwidth_v1 = (2.0 * bytes) / (time_v1 * 1e-3) / 1e9;
    double bandwidth_v2 = (2.0 * bytes) / (time_v2 * 1e-3) / 1e9;
    double speedup = time_v1 / time_v2;
    
    std::ofstream output_file(output_filename);
    if (!output_file.is_open()) {
        std::ofstream err_file("benchmark_error.log", std::ios::app);
        err_file << "Failed to open output file: " << output_filename << std::endl;
        return 1;
    }
    
    output_file << std::fixed << std::setprecision(6);
    output_file << "{\n";
    output_file << "  \"device\": \"" << prop.name << "\",\n";
    output_file << "  \"elements\": " << n << ",\n";
    output_file << "  \"iterations\": " << iterations << ",\n";
    output_file << "  \"block_size\": " << block_size << ",\n";
    output_file << "  \"grid_size\": " << grid.x << ",\n";
    output_file << "  \"results\": {\n";
    output_file << "    \"kernel_v1\": {\n";
    output_file << "      \"time_ms\": " << time_v1 << ",\n";
    output_file << "      \"bandwidth_gb_s\": " << bandwidth_v1 << "\n";
    output_file << "    },\n";
    output_file << "    \"kernel_v2\": {\n";
    output_file << "      \"time_ms\": " << time_v2 << ",\n";
    output_file << "      \"bandwidth_gb_s\": " << bandwidth_v2 << "\n";
    output_file << "    },\n";
    output_file << "    \"speedup_v2_over_v1\": " << speedup << "\n";
    output_file << "  }\n";
    output_file << "}\n";
    
    output_file.close();
    
    HIP_CHECK(hipFree(d_input));
    HIP_CHECK(hipFree(d_output));
    
    return 0;
}

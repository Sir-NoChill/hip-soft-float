#include <hip/hip_runtime.h>
#include <iostream>
#include <vector>
#include <chrono>
#include <random>
#include <iomanip>

#define HIP_CHECK(call) \
    do { \
        hipError_t err = call; \
        if (err != hipSuccess) { \
            std::cerr << "HIP error at " << __FILE__ << ":" << __LINE__ << " - " << hipGetErrorString(err) << std::endl; \
            exit(1); \
        } \
    } while(0)

__global__ void fp32_throughput_kernel(float* input1, float* input2, float* output, size_t n) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float a = input1[idx];
        float b = input2[idx];
        for (int i = 0; i < 100; i++) {
            a = a * b + a;
            b = b * a - b;
        }
        output[idx] = a + b;
    }
}

__global__ void int8_throughput_kernel(int8_t* input1, int8_t* input2, int8_t* output, size_t n) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        int8_t a = input1[idx];
        int8_t b = input2[idx];
        for (int i = 0; i < 100; i++) {
            a = (a * b + a) & 0x7F;
            b = (b * a - b) & 0x7F;
        }
        output[idx] = a + b;
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

void generate_fp32_data(std::vector<float>& data, size_t n) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<float> dis(-100.0f, 100.0f);
    
    for (size_t i = 0; i < n; i++) {
        data[i] = dis(gen);
    }
}

void generate_int8_data(std::vector<int8_t>& data, size_t n) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> dis(-127, 127);
    
    for (size_t i = 0; i < n; i++) {
        data[i] = static_cast<int8_t>(dis(gen));
    }
}

double benchmark_fp32(size_t n, int iterations) {
    std::vector<float> h_input1(n), h_input2(n), h_output(n);
    generate_fp32_data(h_input1, n);
    generate_fp32_data(h_input2, n);

    float *d_input1, *d_input2, *d_output;
    size_t bytes = n * sizeof(float);
    HIP_CHECK(hipMalloc(&d_input1, bytes));
    HIP_CHECK(hipMalloc(&d_input2, bytes));
    HIP_CHECK(hipMalloc(&d_output, bytes));

    HIP_CHECK(hipMemcpy(d_input1, h_input1.data(), bytes, hipMemcpyHostToDevice));
    HIP_CHECK(hipMemcpy(d_input2, h_input2.data(), bytes, hipMemcpyHostToDevice));

    const int block_size = 256;
    dim3 block(block_size);
    dim3 grid((n + block_size - 1) / block_size);

    for (int i = 0; i < 5; i++) {
        hipLaunchKernelGGL(fp32_throughput_kernel, grid, block, 0, 0, d_input1, d_input2, d_output, n);
        HIP_CHECK(hipDeviceSynchronize());
    }

    GPUTimer timer;
    double total_time = 0.0;

    for (int i = 0; i < iterations; i++) {
        timer.start();
        hipLaunchKernelGGL(fp32_throughput_kernel, grid, block, 0, 0, d_input1, d_input2, d_output, n);
        total_time += timer.stop();
    }

    HIP_CHECK(hipFree(d_input1));
    HIP_CHECK(hipFree(d_input2));
    HIP_CHECK(hipFree(d_output));

    return total_time / iterations;
}

double benchmark_int8(size_t n, int iterations) {
    std::vector<int8_t> h_input1(n), h_input2(n), h_output(n);
    generate_int8_data(h_input1, n);
    generate_int8_data(h_input2, n);

    int8_t *d_input1, *d_input2, *d_output;
    size_t bytes = n * sizeof(int8_t);
    HIP_CHECK(hipMalloc(&d_input1, bytes));
    HIP_CHECK(hipMalloc(&d_input2, bytes));
    HIP_CHECK(hipMalloc(&d_output, bytes));

    HIP_CHECK(hipMemcpy(d_input1, h_input1.data(), bytes, hipMemcpyHostToDevice));
    HIP_CHECK(hipMemcpy(d_input2, h_input2.data(), bytes, hipMemcpyHostToDevice));

    const int block_size = 256;
    dim3 block(block_size);
    dim3 grid((n + block_size - 1) / block_size);

    for (int i = 0; i < 5; i++) {
        hipLaunchKernelGGL(int8_throughput_kernel, grid, block, 0, 0, d_input1, d_input2, d_output, n);
        HIP_CHECK(hipDeviceSynchronize());
    }

    GPUTimer timer;
    double total_time = 0.0;

    for (int i = 0; i < iterations; i++) {
        timer.start();
        hipLaunchKernelGGL(int8_throughput_kernel, grid, block, 0, 0, d_input1, d_input2, d_output, n);
        total_time += timer.stop();
    }

    HIP_CHECK(hipFree(d_input1));
    HIP_CHECK(hipFree(d_input2));
    HIP_CHECK(hipFree(d_output));

    return total_time / iterations;
}

int main(int argc, char** argv) {
    const size_t n = (argc > 1) ? std::stoull(argv[1]) : 1024 * 1024 * 16;
    const int iterations = (argc > 2) ? std::stoi(argv[2]) : 100;

    hipDeviceProp_t prop;
    HIP_CHECK(hipGetDeviceProperties(&prop, 0));

    double fp32_time = benchmark_fp32(n, iterations);
    double int8_time = benchmark_int8(n, iterations);

    size_t fp32_ops_per_element = 200;
    size_t int8_ops_per_element = 200;
    
    double fp32_gops = (static_cast<double>(n) * fp32_ops_per_element) / (fp32_time * 1e-3) / 1e9;
    double int8_gops = (static_cast<double>(n) * int8_ops_per_element) / (int8_time * 1e-3) / 1e9;

    std::cout << std::fixed << std::setprecision(3);
    std::cout << "Device: " << prop.name << std::endl;
    std::cout << "Elements: " << n << std::endl;
    std::cout << "Iterations: " << iterations << std::endl;
    std::cout << "FP32 Time (ms): " << fp32_time << std::endl;
    std::cout << "FP32 GOPS: " << fp32_gops << std::endl;
    std::cout << "INT8 Time (ms): " << int8_time << std::endl;
    std::cout << "INT8 GOPS: " << int8_gops << std::endl;
    std::cout << "INT8/FP32 Speedup: " << fp32_time / int8_time << std::endl;

    return 0;
}
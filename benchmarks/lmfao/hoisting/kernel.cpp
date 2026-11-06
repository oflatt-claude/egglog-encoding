// Execution probe for the prepared bags of the original covariance query q20.
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <vector>

struct Block { uint64_t begin, end; double oil; };
struct Data { std::vector<double> sales; std::vector<Block> blocks; };

template<class T> T read(std::ifstream& input) {
    T value;
    if (!input.read(reinterpret_cast<char*>(&value), sizeof(value)))
        throw std::runtime_error("truncated input");
    return value;
}

// KERNEL

int main(int argc, char** argv) {
    if (argc != 4) return 2;
    std::ifstream input(argv[1], std::ios::binary);
    Data data;
    const auto sales = read<uint64_t>(input);
    data.sales.resize(sales);
    if (!input.read(reinterpret_cast<char*>(data.sales.data()), sales * sizeof(double))) return 3;
    const auto blocks = read<uint64_t>(input);
    for (uint64_t i = 0; i < blocks; ++i) {
        Block block{read<uint64_t>(input), read<uint64_t>(input), read<double>(input)};
        if (block.begin > block.end || block.end > sales) return 4;
        data.blocks.push_back(block);
    }
    const double expected = std::stod(argv[2]);
    const int repeats = std::stoi(argv[3]);
    const double answer = kernel(data); // Validate and warm before measuring.
    if (!std::isfinite(answer) || std::abs(answer - expected) > 1e-7 + 1e-9 * std::abs(expected)) return 5;
    const auto start = std::chrono::steady_clock::now();
    double checksum = 0;
    for (int i = 0; i < repeats; ++i) {
        asm volatile("" : : "g"(data.sales.data()) : "memory");
        checksum += kernel(data);
    }
    const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    std::cout << std::setprecision(17) << "{\"answer\":" << answer
              << ",\"checksum\":" << checksum << ",\"seconds_per_query\":" << seconds / repeats << "}\n";
}

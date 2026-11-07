// Execution probe over prepared bags of original covariance queries.
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <vector>

struct Block { uint64_t begin, end; double oil; };
using Sale = std::array<double, SALES_WIDTH>;
using Answers = std::array<double, OUTPUTS>;
struct Data { std::vector<Sale> sales; std::vector<Block> blocks; };

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
    if (!input.read(reinterpret_cast<char*>(data.sales.data()), sales * sizeof(Sale))) return 3;
    const auto blocks = read<uint64_t>(input);
    for (uint64_t i = 0; i < blocks; ++i) {
        Block block{read<uint64_t>(input), read<uint64_t>(input), read<double>(input)};
        if (block.begin > block.end || block.end > sales) return 4;
        data.blocks.push_back(block);
    }
    Answers expected;
    std::ifstream oracle(argv[2]);
    for (auto& value : expected) if (!(oracle >> value)) return 5;
    const int repeats = std::stoi(argv[3]);
    const auto answer = kernel(data); // Validate and warm before measuring.
    for (size_t i = 0; i < answer.size(); ++i)
        if (!std::isfinite(answer[i]) || std::abs(answer[i] - expected[i]) > 1e-7 + 1e-9 * std::abs(expected[i])) return 6;
    const auto start = std::chrono::steady_clock::now();
    double checksum = 0;
    for (int i = 0; i < repeats; ++i) {
        asm volatile("" : : "g"(data.sales.data()) : "memory");
        for (auto value : kernel(data)) checksum += value;
    }
    const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    std::cout << std::setprecision(17) << "{\"answer\":[";
    for (size_t i = 0; i < answer.size(); ++i) std::cout << (i ? "," : "") << answer[i];
    std::cout << "],\"checksum\":" << checksum << ",\"seconds_per_execution\":" << seconds / repeats << "}\n";
}

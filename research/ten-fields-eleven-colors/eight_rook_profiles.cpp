// Enumerate coefficient maxima by multiplicity partition for eight cylindrical
// rooks.  This is an audit/discovery program for the cofactor proof table.

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

using Eight = std::array<int, 8>;

struct Record {
  int count = 0;
  Eight positions{};
  Eight colors{};
  std::array<int, 11> histogram{};
};

std::string shape(const std::array<int, 11>& histogram) {
  std::vector<int> parts;
  for (int value : histogram) {
    if (value != 0) parts.push_back(value);
  }
  std::sort(parts.rbegin(), parts.rend());
  std::ostringstream out;
  for (std::size_t i = 0; i < parts.size(); ++i) {
    if (i != 0) out << '+';
    out << parts[i];
  }
  return out.str();
}

std::string set_string(const Eight& values) {
  std::ostringstream out;
  for (int value : values) out << value;
  return out.str();
}

std::string diagonals(const std::array<int, 11>& histogram) {
  std::ostringstream out;
  bool first = true;
  for (int d = 0; d < 11; ++d) {
    for (int multiplicity = 0; multiplicity < histogram[d]; ++multiplicity) {
      if (!first) out << ',';
      first = false;
      out << d;
    }
  }
  return out.str();
}

int main() {
  std::map<std::string, Record> maxima;
  std::array<int, 11> choose_positions{};
  choose_positions.fill(0);
  std::fill_n(choose_positions.begin(), 8, 1);
  // Normalize by requiring position 10 to be omitted.  Every translation
  // orbit has such a representative because three positions are omitted.
  choose_positions[10] = 0;

  do {
    if (std::accumulate(choose_positions.begin(), choose_positions.end(), 0) != 8)
      continue;
    Eight positions{};
    int pi = 0;
    for (int i = 0; i < 11; ++i)
      if (choose_positions[i]) positions[pi++] = i;

    std::array<int, 11> choose_colors{};
    choose_colors.fill(0);
    std::fill_n(choose_colors.begin(), 8, 1);
    do {
      // Color translation also only shifts all diagonal labels, so normalize
      // the color set independently by requiring color 10 to be omitted.
      if (choose_colors[10]) continue;
      Eight colors{};
      int ci = 0;
      for (int c = 0; c < 11; ++c)
        if (choose_colors[c]) colors[ci++] = c;

      std::unordered_map<std::uint64_t, int> coefficients;
      coefficients.reserve(40320);
      Eight permutation = colors;
      do {
        std::array<int, 11> histogram{};
        std::uint64_t key = 0;
        for (int i = 0; i < 8; ++i) {
          const int d = (permutation[i] - positions[i] + 11) % 11;
          ++histogram[d];
        }
        for (int d = 0; d < 11; ++d) key = key * 9 + histogram[d];
        ++coefficients[key];
      } while (std::next_permutation(permutation.begin(), permutation.end()));
      for (const auto& [key, count] : coefficients) {
        std::array<int, 11> histogram{};
        std::uint64_t remaining = key;
        for (int d = 10; d >= 0; --d) {
          histogram[d] = remaining % 9;
          remaining /= 9;
        }
        auto& record = maxima[shape(histogram)];
        if (count > record.count) {
          record = {count, positions, colors, histogram};
        }
      }
    } while (std::prev_permutation(choose_colors.begin(), choose_colors.end()));
  } while (std::prev_permutation(choose_positions.begin(), choose_positions.end()));

  for (const auto& [partition, record] : maxima) {
    std::cout << partition << " | " << record.count << " | P="
              << set_string(record.positions) << " C="
              << set_string(record.colors) << " D="
              << diagonals(record.histogram) << '\n';
  }
}

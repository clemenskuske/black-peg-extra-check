// Exact verifier for the normalized eight-rook cylindrical Sep 3 claim.
//
// This is still an audit/certificate-production precursor, not a Lean proof.
// It checks every affine-normalized support pair and every diagonal fiber
// using the same game predicate as `Separator.Sep`: choose a legal query,
// observe black, then choose one equality edge for both Boolean children.
// Queries are restricted to current candidate bijections, which is a sound
// existence search because each candidate row is a legal query on the open
// rook positions and can be extended over the fixed fields.

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {

constexpr int N = 11;
constexpr int R = 8;
constexpr int WORD_BITS = 64;

using Eight = std::array<int, R>;
using Hist = std::array<int, N>;

struct Mask {
  std::vector<std::uint64_t> words;

  Mask() = default;
  explicit Mask(std::size_t word_count) : words(word_count, 0) {}

  bool empty() const {
    for (std::uint64_t word : words)
      if (word != 0) return false;
    return true;
  }

  int count() const {
    int total = 0;
    for (std::uint64_t word : words) total += __builtin_popcountll(word);
    return total;
  }

  bool get(int index) const {
    return (words[index / WORD_BITS] >> (index % WORD_BITS)) & 1ULL;
  }

  void set(int index) {
    words[index / WORD_BITS] |= 1ULL << (index % WORD_BITS);
  }

  std::string key(int depth) const {
    std::string out;
    out.reserve(1 + words.size() * sizeof(std::uint64_t));
    out.push_back(static_cast<char>(depth));
    for (std::uint64_t word : words) {
      for (int i = 0; i < 8; ++i) {
        out.push_back(static_cast<char>((word >> (8 * i)) & 0xff));
      }
    }
    return out;
  }
};

Mask intersect_mask(const Mask& a, const Mask& b) {
  Mask result(a.words.size());
  for (std::size_t i = 0; i < a.words.size(); ++i)
    result.words[i] = a.words[i] & b.words[i];
  return result;
}

Mask subtract_mask(const Mask& a, const Mask& b) {
  Mask result(a.words.size());
  for (std::size_t i = 0; i < a.words.size(); ++i)
    result.words[i] = a.words[i] & ~b.words[i];
  return result;
}

std::uint64_t hist_key(const Hist& h) {
  std::uint64_t key = 0;
  for (int d = 0; d < N; ++d) key = key * 9 + h[d];
  return key;
}

std::vector<Eight> support_representatives() {
  return {
      Eight{0, 1, 2, 3, 4, 5, 6, 7},
      Eight{0, 1, 2, 3, 4, 5, 6, 8},
  };
}

struct FiberVerifier {
  Eight positions;
  Eight colors;
  std::vector<Eight> candidates;
  std::vector<std::array<Mask, R + 1>> black_masks;
  std::vector<Mask> edge_masks;
  std::unordered_map<std::string, bool> memo;

  explicit FiberVerifier(Eight p, Eight c, std::vector<Eight> rows)
      : positions(p), colors(c), candidates(std::move(rows)) {
    const std::size_t words = (candidates.size() + WORD_BITS - 1) / WORD_BITS;
    black_masks.resize(candidates.size());
    for (auto& per_query : black_masks)
      for (auto& mask : per_query) mask = Mask(words);

    for (std::size_t q = 0; q < candidates.size(); ++q) {
      for (std::size_t s = 0; s < candidates.size(); ++s) {
        int matches = 0;
        for (int i = 0; i < R; ++i)
          if (candidates[q][i] == candidates[s][i]) ++matches;
        black_masks[q][matches].set(static_cast<int>(s));
      }
    }

    for (int pos = 0; pos < R; ++pos) {
      for (int color : colors) {
        Mask mask(words);
        for (std::size_t s = 0; s < candidates.size(); ++s)
          if (candidates[s][pos] == color) mask.set(static_cast<int>(s));
        edge_masks.push_back(std::move(mask));
      }
    }
  }

  Mask full_mask() const {
    Mask mask((candidates.size() + WORD_BITS - 1) / WORD_BITS);
    for (std::size_t i = 0; i < candidates.size(); ++i)
      mask.set(static_cast<int>(i));
    return mask;
  }

  bool sep(int depth, const Mask& state) {
    const int state_size = state.count();
    if (state_size <= 1) return true;
    if (depth == 0) return false;
    const std::string key = state.key(depth);
    if (auto found = memo.find(key); found != memo.end()) return found->second;

    if (depth == 1) {
      for (std::size_t q = 0; q < candidates.size(); ++q) {
        if (!state.get(static_cast<int>(q))) continue;
        bool good = true;
        for (int b = 0; b <= R; ++b) {
          if (intersect_mask(state, black_masks[q][b]).count() > 2) {
            good = false;
            break;
          }
        }
        if (good) return memo.emplace(key, true).first->second;
      }
      return memo.emplace(key, false).first->second;
    }

    for (std::size_t q = 0; q < candidates.size(); ++q) {
      if (!state.get(static_cast<int>(q))) continue;
      bool query_good = true;
      for (int b = 0; b <= R; ++b) {
        Mask black = intersect_mask(state, black_masks[q][b]);
        if (black.empty()) continue;
        bool edge_good = false;
        for (const Mask& edge : edge_masks) {
          Mask yes = intersect_mask(black, edge);
          Mask no = subtract_mask(black, edge);
          if (sep(depth - 1, yes) && sep(depth - 1, no)) {
            edge_good = true;
            break;
          }
        }
        if (!edge_good) {
          query_good = false;
          break;
        }
      }
      if (query_good) return memo.emplace(key, true).first->second;
    }
    return memo.emplace(key, false).first->second;
  }
};

}  // namespace

int main() {
  const auto started = std::chrono::steady_clock::now();
  const std::vector<Eight> reps = support_representatives();

  std::uint64_t support_pairs = 0;
  std::uint64_t fibers_checked = 0;
  std::uint64_t total_memberships = 0;
  std::uint64_t large_fibers = 0;
  std::uint64_t unsolved = 0;
  std::size_t max_fiber = 0;

  std::cout << "position representatives: " << reps.size() << '\n';
  std::cout << "color representatives: " << reps.size() << '\n';

  for (const Eight& positions : reps) {
    for (const Eight& colors : reps) {
      ++support_pairs;
      std::unordered_map<std::uint64_t, std::vector<Eight>> fibers;
      fibers.reserve(10000);

      Eight permutation = colors;
      do {
        Hist h{};
        for (int i = 0; i < R; ++i) {
          const int d = (permutation[i] - positions[i] + N) % N;
          ++h[d];
        }
        fibers[hist_key(h)].push_back(permutation);
      } while (std::next_permutation(permutation.begin(), permutation.end()));

      for (auto& [_, rows] : fibers) {
        ++fibers_checked;
        total_memberships += rows.size();
        max_fiber = std::max(max_fiber, rows.size());
        if (rows.size() >= 4) ++large_fibers;

        if (rows.size() > 1) {
          FiberVerifier verifier(positions, colors, std::move(rows));
          if (!verifier.sep(3, verifier.full_mask())) {
            ++unsolved;
            std::cerr << "unsolved fiber of size "
                      << verifier.candidates.size() << '\n';
            return EXIT_FAILURE;
          }
        }
      }
    }
  }

  const auto finished = std::chrono::steady_clock::now();
  const double seconds =
      std::chrono::duration_cast<std::chrono::duration<double>>(
          finished - started)
          .count();

  std::cout << "normalized support pairs: " << support_pairs << '\n';
  std::cout << "fibers checked: " << fibers_checked << '\n';
  std::cout << "total fiber memberships: " << total_memberships << '\n';
  std::cout << "maximum fiber size: " << max_fiber << '\n';
  std::cout << "fibers of size >= 4: " << large_fibers << '\n';
  std::cout << "not solved in three rounds: " << unsolved << '\n';
  std::cout << "elapsed seconds: " << seconds << '\n';
}

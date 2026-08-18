// Exact verifier for the compatible-affine-normalized eight-rook cylindrical
// Sep 3 claim.
//
// This is still an audit/certificate-production precursor, not a Lean proof.
// It checks every support-pair orbit under exactly
//
//   p |-> a*p+s,   c |-> a*c+t       (a nonzero mod 11)
//
// with one common multiplier `a` and independent translations `s,t`.  This is
// the compatible group for cylindrical displacement histograms: c-p is then
// relabeled as a*(c-p)+(t-s).  Independent position/color multipliers are not
// used, because they do not preserve displacement labels.
//
// For each canonical support pair it checks every exact diagonal fiber using
// the same game predicate as `Separator.Sep`: choose a legal query, observe
// black, then choose one equality edge, and require both Boolean children.
// Queries are restricted to current candidate bijections, which is a sound
// existence search because each candidate row is a legal query on the open
// rook positions and can be extended over the fixed fields.

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace {

constexpr int N = 11;
constexpr int R = 8;
constexpr int WORD_BITS = 64;
constexpr int EXPECTED_SUPPORTS = 165;
constexpr int EXPECTED_RAW_SUPPORT_PAIRS = EXPECTED_SUPPORTS * EXPECTED_SUPPORTS;
constexpr int EXPECTED_COMPATIBLE_GROUP_SIZE = (N - 1) * N * N;
constexpr int EXPECTED_SHARP_FIBER_SIZE = 86;

using Support = std::array<int, R>;
using SupportPair = std::pair<Support, Support>;
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

Hist decode_hist_key(std::uint64_t key) {
  Hist histogram{};
  for (int d = N - 1; d >= 0; --d) {
    histogram[d] = static_cast<int>(key % 9);
    key /= 9;
  }
  return histogram;
}

std::string support_string(const Support& support) {
  std::ostringstream out;
  out << '{';
  for (int i = 0; i < R; ++i) {
    if (i != 0) out << ',';
    out << support[i];
  }
  out << '}';
  return out.str();
}

std::string hist_string(const Hist& histogram) {
  std::ostringstream out;
  out << '{';
  bool first = true;
  for (int d = 0; d < N; ++d) {
    for (int i = 0; i < histogram[d]; ++i) {
      if (!first) out << ',';
      first = false;
      out << d;
    }
  }
  out << '}';
  return out.str();
}

[[noreturn]] void fail(const std::string& message) {
  std::cerr << "verify_eight_rook_sep3: " << message << '\n';
  std::exit(EXIT_FAILURE);
}

std::vector<Support> all_supports() {
  std::vector<Support> supports;
  for (int mask = 0; mask < (1 << N); ++mask) {
    if (__builtin_popcount(static_cast<unsigned>(mask)) != R) continue;
    Support support{};
    int out = 0;
    for (int x = 0; x < N; ++x) {
      if ((mask >> x) & 1) support[out++] = x;
    }
    supports.push_back(support);
  }
  if (static_cast<int>(supports.size()) != EXPECTED_SUPPORTS) {
    fail("expected 165 eight-element supports, got " +
         std::to_string(supports.size()));
  }
  return supports;
}

int affine(int x, int multiplier, int translation) {
  return (multiplier * x + translation) % N;
}

Support transform_support(const Support& support, int multiplier,
                          int translation) {
  Support result{};
  for (int i = 0; i < R; ++i)
    result[i] = affine(support[i], multiplier, translation);
  std::sort(result.begin(), result.end());
  return result;
}

SupportPair transform_pair(const SupportPair& pair, int multiplier,
                           int position_translation,
                           int color_translation) {
  return {transform_support(pair.first, multiplier, position_translation),
          transform_support(pair.second, multiplier, color_translation)};
}

Hist transform_hist(const Hist& histogram, int multiplier,
                    int displacement_translation) {
  Hist result{};
  for (int d = 0; d < N; ++d) {
    result[affine(d, multiplier, displacement_translation)] = histogram[d];
  }
  return result;
}

SupportPair canonical_pair(const Support& positions, const Support& colors) {
  const SupportPair original{positions, colors};
  SupportPair best = transform_pair(original, 1, 0, 0);
  for (int multiplier = 1; multiplier < N; ++multiplier) {
    for (int position_translation = 0; position_translation < N;
         ++position_translation) {
      for (int color_translation = 0; color_translation < N;
           ++color_translation) {
        best = std::min(best, transform_pair(original, multiplier,
                                             position_translation,
                                             color_translation));
      }
    }
  }
  return best;
}

std::map<SupportPair, std::uint64_t> canonical_support_pairs(
    const std::vector<Support>& supports) {
  std::set<SupportPair> raw_pairs;
  std::map<SupportPair, std::uint64_t> orbit_sizes;
  for (const Support& positions : supports) {
    for (const Support& colors : supports) {
      const SupportPair pair{positions, colors};
      raw_pairs.insert(pair);
      ++orbit_sizes[canonical_pair(positions, colors)];
    }
  }

  if (static_cast<int>(raw_pairs.size()) != EXPECTED_RAW_SUPPORT_PAIRS) {
    fail("expected 27225 raw support pairs, got " +
         std::to_string(raw_pairs.size()));
  }

  std::uint64_t orbit_total = 0;
  std::set<SupportPair> covered;
  for (const auto& [canonical, expected_orbit_size] : orbit_sizes) {
    if (canonical_pair(canonical.first, canonical.second) != canonical) {
      fail("noncanonical representative survived orbit map");
    }

    std::set<SupportPair> orbit;
    for (int multiplier = 1; multiplier < N; ++multiplier) {
      for (int position_translation = 0; position_translation < N;
           ++position_translation) {
        for (int color_translation = 0; color_translation < N;
             ++color_translation) {
          orbit.insert(transform_pair(canonical, multiplier,
                                      position_translation,
                                      color_translation));
        }
      }
    }

    if (orbit.size() != expected_orbit_size) {
      fail("orbit size mismatch for P=" + support_string(canonical.first) +
           " C=" + support_string(canonical.second) + ": canonical count " +
           std::to_string(expected_orbit_size) + ", generated orbit " +
           std::to_string(orbit.size()));
    }

    for (const SupportPair& member : orbit) {
      if (!raw_pairs.contains(member)) {
        fail("generated orbit member is not a raw support pair");
      }
      if (canonical_pair(member.first, member.second) != canonical) {
        fail("orbit member canonicalizes to a different representative");
      }
      covered.insert(member);
    }

    orbit_total += expected_orbit_size;
  }

  if (orbit_total != EXPECTED_RAW_SUPPORT_PAIRS ||
      covered.size() != raw_pairs.size()) {
    fail("compatible orbit coverage incomplete: orbit total " +
         std::to_string(orbit_total) + ", covered " +
         std::to_string(covered.size()) + ", raw " +
         std::to_string(raw_pairs.size()));
  }

  return orbit_sizes;
}

std::unordered_map<std::uint64_t, std::vector<Support>> build_fibers(
    const Support& positions, const Support& colors) {
  std::unordered_map<std::uint64_t, std::vector<Support>> fibers;
  fibers.reserve(10000);

  Support permutation = colors;
  do {
    Hist h{};
    for (int i = 0; i < R; ++i) {
      const int d = (permutation[i] - positions[i] + N) % N;
      ++h[d];
    }
    fibers[hist_key(h)].push_back(permutation);
  } while (std::next_permutation(permutation.begin(), permutation.end()));

  return fibers;
}

struct SharpRegression {
  SupportPair canonical;
  std::set<std::uint64_t> canonical_hist_keys;
};

SharpRegression verify_sharp_regression() {
  const Support sharp_positions{0, 1, 2, 3, 4, 5, 6, 7};
  const Support sharp_colors{0, 1, 2, 3, 4, 6, 7, 9};
  Hist sharp_hist{};
  for (int d : {0, 1, 2, 4, 6, 7, 8, 9}) ++sharp_hist[d];

  const auto sharp_fibers = build_fibers(sharp_positions, sharp_colors);
  const auto found = sharp_fibers.find(hist_key(sharp_hist));
  if (found == sharp_fibers.end()) {
    fail("known sharp fiber histogram was not generated");
  }
  if (static_cast<int>(found->second.size()) != EXPECTED_SHARP_FIBER_SIZE) {
    fail("known sharp fiber should have size 86, got " +
         std::to_string(found->second.size()));
  }

  const SupportPair sharp_pair{sharp_positions, sharp_colors};
  SharpRegression regression{canonical_pair(sharp_positions, sharp_colors), {}};
  for (int multiplier = 1; multiplier < N; ++multiplier) {
    for (int position_translation = 0; position_translation < N;
         ++position_translation) {
      for (int color_translation = 0; color_translation < N;
           ++color_translation) {
        if (transform_pair(sharp_pair, multiplier, position_translation,
                           color_translation) == regression.canonical) {
          const int displacement_translation =
              (color_translation - position_translation + N) % N;
          regression.canonical_hist_keys.insert(hist_key(transform_hist(
              sharp_hist, multiplier, displacement_translation)));
        }
      }
    }
  }
  if (regression.canonical_hist_keys.empty()) {
    fail("sharp support pair did not map to its canonical representative");
  }
  return regression;
}

struct FiberVerifier {
  struct Choice {
    bool solvable = false;
    int query = -1;
    std::array<int, R + 1> edge{};
  };

  Support positions;
  Support colors;
  std::vector<Support> candidates;
  std::vector<std::array<Mask, R + 1>> black_masks;
  std::vector<Mask> edge_masks;
  std::unordered_map<std::string, Choice> memo;

  explicit FiberVerifier(Support p, Support c, std::vector<Support> rows)
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

  Choice one_round(const Mask& state) {
    for (std::size_t q = 0; q < candidates.size(); ++q) {
      if (!state.get(static_cast<int>(q))) continue;
      Choice choice;
      choice.solvable = true;
      choice.query = static_cast<int>(q);
      bool query_good = true;
      for (int b = 0; b <= R; ++b) {
        Mask black = intersect_mask(state, black_masks[q][b]);
        if (black.empty()) continue;
        bool edge_good = false;
        for (std::size_t edge_index = 0; edge_index < edge_masks.size();
             ++edge_index) {
          Mask yes = intersect_mask(black, edge_masks[edge_index]);
          Mask no = subtract_mask(black, edge_masks[edge_index]);
          if (yes.count() <= 1 && no.count() <= 1) {
            edge_good = true;
            choice.edge[b] = static_cast<int>(edge_index);
            break;
          }
        }
        if (!edge_good) {
          query_good = false;
          break;
        }
      }
      if (query_good) return choice;
    }
    return {};
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
    if (auto found = memo.find(key); found != memo.end())
      return found->second.solvable;

    if (depth == 1) {
      return memo.emplace(key, one_round(state)).first->second.solvable;
    }

    for (std::size_t q = 0; q < candidates.size(); ++q) {
      if (!state.get(static_cast<int>(q))) continue;
      Choice choice;
      choice.solvable = true;
      choice.query = static_cast<int>(q);
      bool query_good = true;
      for (int b = 0; b <= R; ++b) {
        Mask black = intersect_mask(state, black_masks[q][b]);
        if (black.empty()) continue;
        bool edge_good = false;
        for (std::size_t edge_index = 0; edge_index < edge_masks.size();
             ++edge_index) {
          Mask yes = intersect_mask(black, edge_masks[edge_index]);
          Mask no = subtract_mask(black, edge_masks[edge_index]);
          if (sep(depth - 1, yes) && sep(depth - 1, no)) {
            edge_good = true;
            choice.edge[b] = static_cast<int>(edge_index);
            break;
          }
        }
        if (!edge_good) {
          query_good = false;
          break;
        }
      }
      if (query_good) return memo.emplace(key, choice).first->second.solvable;
    }
    return memo.emplace(key, Choice{}).first->second.solvable;
  }

  std::uint64_t reachable_nonterminal_nodes(
      int depth, const Mask& state, std::unordered_set<std::string>& seen) const {
    if (state.count() <= 1 || depth == 0) return 0;
    const std::string key = state.key(depth);
    if (!seen.insert(key).second) return 0;
    const auto found = memo.find(key);
    if (found == memo.end() || !found->second.solvable ||
        found->second.query < 0) {
      fail("solved state is missing a deterministic witness choice");
    }

    std::uint64_t total = 1;
    const Choice& choice = found->second;
    for (int b = 0; b <= R; ++b) {
      const Mask black =
          intersect_mask(state, black_masks[static_cast<std::size_t>(choice.query)][b]);
      const Mask& edge = edge_masks[static_cast<std::size_t>(choice.edge[b])];
      total += reachable_nonterminal_nodes(depth - 1,
          intersect_mask(black, edge), seen);
      total += reachable_nonterminal_nodes(depth - 1,
          subtract_mask(black, edge), seen);
    }
    return total;
  }
};

}  // namespace

int main() {
  const auto started = std::chrono::steady_clock::now();
  const std::vector<Support> supports = all_supports();
  const auto orbit_sizes = canonical_support_pairs(supports);
  const SharpRegression sharp = verify_sharp_regression();

  std::uint64_t support_pairs = 0;
  std::uint64_t fibers_checked = 0;
  std::uint64_t total_memberships = 0;
  std::uint64_t large_fibers = 0;
  std::uint64_t unsolved = 0;
  std::uint64_t total_witness_nodes = 0;
  std::uint64_t max_witness_nodes = 0;
  std::size_t max_fiber = 0;
  SupportPair max_pair{};
  Hist max_hist{};
  std::size_t max_witness_fiber = 0;
  bool sharp_canonical_fiber_seen = false;

  std::cout << "eight-element supports: " << supports.size() << '\n';
  std::cout << "raw support pairs: " << EXPECTED_RAW_SUPPORT_PAIRS << '\n';
  std::cout << "compatible affine group size: "
            << EXPECTED_COMPATIBLE_GROUP_SIZE << '\n';
  std::cout << "canonical support-pair orbits: " << orbit_sizes.size() << '\n';
  std::cout << "orbit completeness: ok\n";
  std::cout << "sharp fiber regression size: " << EXPECTED_SHARP_FIBER_SIZE
            << '\n';

  for (const auto& [pair, _orbit_size] : orbit_sizes) {
    ++support_pairs;
    auto fibers = build_fibers(pair.first, pair.second);

    for (auto& [key, rows] : fibers) {
      ++fibers_checked;
      total_memberships += rows.size();
      if (rows.size() > max_fiber) {
        max_fiber = rows.size();
        max_pair = pair;
        max_hist = decode_hist_key(key);
      }
      if (pair == sharp.canonical &&
          sharp.canonical_hist_keys.contains(key)) {
        if (static_cast<int>(rows.size()) != EXPECTED_SHARP_FIBER_SIZE) {
          fail("canonical image of sharp fiber should have size 86, got " +
               std::to_string(rows.size()));
        }
        sharp_canonical_fiber_seen = true;
      }
      if (rows.size() >= 4) ++large_fibers;

      if (rows.size() > 1) {
        FiberVerifier verifier(pair.first, pair.second, std::move(rows));
        Mask full = verifier.full_mask();
        if (!verifier.sep(3, full)) {
          ++unsolved;
          std::cerr << "unsolved fiber of size "
                    << verifier.candidates.size() << " at P="
                    << support_string(pair.first) << " C="
                    << support_string(pair.second) << " D="
                    << hist_string(decode_hist_key(key)) << '\n';
          return EXIT_FAILURE;
        }
        std::unordered_set<std::string> seen;
        const std::uint64_t witness_nodes =
            verifier.reachable_nonterminal_nodes(3, full, seen);
        total_witness_nodes += witness_nodes;
        if (witness_nodes > max_witness_nodes) {
          max_witness_nodes = witness_nodes;
          max_witness_fiber = verifier.candidates.size();
        }
      }
    }
  }

  if (max_fiber != EXPECTED_SHARP_FIBER_SIZE) {
    fail("expected maximum fiber size 86, got " + std::to_string(max_fiber) +
         " at P=" + support_string(max_pair.first) +
         " C=" + support_string(max_pair.second) +
         " D=" + hist_string(max_hist));
  }
  if (!sharp_canonical_fiber_seen) {
    fail("exhaustive canonical pass did not cover the known sharp fiber");
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
  std::cout << "maximum fiber support P=" << support_string(max_pair.first)
            << " C=" << support_string(max_pair.second)
            << " D=" << hist_string(max_hist) << '\n';
  std::cout << "sharp fiber covered by canonical orbit: yes\n";
  std::cout << "chosen separator DAG nonterminal nodes: "
            << total_witness_nodes << '\n';
  std::cout << "maximum chosen separator DAG nonterminal nodes: "
            << max_witness_nodes << " for fiber size "
            << max_witness_fiber << '\n';
  std::cout << "fibers of size >= 4: " << large_fibers << '\n';
  std::cout << "not solved in three rounds: " << unsolved << '\n';
  std::cout << "elapsed seconds: " << seconds << '\n';
}

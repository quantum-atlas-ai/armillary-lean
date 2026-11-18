// Generate untrusted reduced-support exclusion programs for routed Armillary codes.
// Opcode 3 records a stabilizer row intersecting the current support more than six times.
// Opcode 4 records a packing of original and pairwise XOR parity rows.
// Each stdout line contains one complete program in anchor order.

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>

constexpr int rows = 2172;
constexpr int cols = 8688;
std::array<std::array<int, 3>, cols> stabilizers{};
std::array<int, rows> overlaps{};
bool outputWords = true;
bool binaryWords = false;
bool useXorPacking = false;
std::array<std::array<int, 12>, rows> neighbors;
std::array<std::array<int, 3>, cols> checks;
std::array<bool, cols> marked{};
std::array<bool, rows> odd{};
std::vector<int> selected;
std::vector<int> odds;
std::array<int, rows> location;
std::array<unsigned, cols> taken{};
unsigned stamp = 0;
uint64_t nodes = 0;
uint64_t leaves = 0;
std::vector<uint16_t> words;
uint64_t wordCount = 0;
void emit(std::initializer_list<int> data) {
  wordCount += data.size();
  if (outputWords) words.insert(words.end(), data.begin(), data.end());
}

void toggle(int col) {
  for (int row : checks[col]) {
    odd[row] = !odd[row];
    if (odd[row]) {
      location[row] = odds.size();
      odds.push_back(row);
    } else {
      location[odds.back()] = location[row];
      odds[location[row]] = odds.back();
      odds.pop_back();
    }
  }
}

bool independent(uint32_t candidates, int need, const std::array<uint32_t, 32>& conflict,
                 std::vector<int>& witness) {
  if (need == 0) return true;
  while (std::popcount(candidates) >= need) {
    int chosen = 0;
    int fewest_conflicts = 33;
    for (uint32_t scan = candidates; scan; scan &= scan - 1) {
      int index = std::countr_zero(scan);
      int count = std::popcount(conflict[index] & candidates);
      if (count < fewest_conflicts) {
        chosen = index;
        fewest_conflicts = count;
      }
    }
    candidates &= ~(uint32_t{1} << chosen);
    witness.push_back(odds[chosen]);
    if (independent(candidates & ~conflict[chosen], need - 1, conflict, witness)) return true;
    witness.pop_back();
    if (fewest_conflicts == 0) return false;
  }
  return false;
}

bool strong_packing(int remaining, std::vector<int>& witness) {
  int count = odds.size();
  if (count <= remaining || count >= 32) return false;
  std::array<uint32_t, 32> conflict{};
  for (int index = 0; index < count; ++index) {
    for (int column : neighbors[odds[index]]) {
      if (marked[column]) continue;
      for (int other : checks[column]) {
        if (odd[other] && location[other] != index) {
          conflict[index] |= uint32_t{1} << location[other];
        }
      }
    }
  }
  return independent((uint32_t{1} << count) - 1, remaining + 1, conflict, witness);
}

void emit_packing(const std::vector<int>& packing) {
  ++leaves;
  emit({1, static_cast<int>(packing.size())});
  wordCount += packing.size();
  if (outputWords) words.insert(words.end(), packing.begin(), packing.end());
}

void fresh_stamp() {
  if (++stamp == 0) {
    taken.fill(0);
    ++stamp;
  }
}

struct PackingRow {
  int first;
  int second;  // -1 denotes an uncombined row.
  std::vector<int> available;
};

void append_difference(int first, int second, std::vector<int>& available) {
  const auto& excluded = neighbors[second];
  for (int col : neighbors[first]) {
    if (!marked[col] && std::find(excluded.begin(), excluded.end(), col) == excluded.end()) {
      available.push_back(col);
    }
  }
}

bool xor_packing(int remaining) {
  if (static_cast<int>(odds.size()) <= remaining) return false;
  std::vector<PackingRow> pool;
  for (int row : odds) {
    PackingRow plain{row, -1, {}};
    for (int col : neighbors[row]) if (!marked[col]) plain.available.push_back(col);
    pool.push_back(std::move(plain));

    // Cancel a column shared by two odd rows using its third, even row.
    for (int col : neighbors[row]) {
      if (marked[col]) continue;
      int even = -1;
      int active = 0;
      for (int other : checks[col]) {
        if (odd[other]) ++active;
        else even = other;
      }
      if (active != 2) continue;
      PackingRow combined{row, even, {}};
      append_difference(row, even, combined.available);
      append_difference(even, row, combined.available);
      pool.push_back(std::move(combined));
    }
  }
  if (pool.size() == odds.size()) return false;
  std::vector<int> order(pool.size());
  std::iota(order.begin(), order.end(), 0);
  std::sort(order.begin(), order.end(), [&](int a, int b) {
    return pool[a].available.size() < pool[b].available.size();
  });
  for (int pivot = 0; pivot < static_cast<int>(pool.size()); ++pivot) {
    if (pool[pivot].second < 0) continue;
    fresh_stamp();
    for (int col : pool[pivot].available) taken[col] = stamp;
    std::vector<int> picked{pivot};
    for (int index : order) {
      if (index == pivot) continue;
      const auto& available = pool[index].available;
      if (std::any_of(available.begin(), available.end(),
                      [](int col) { return taken[col] == stamp; })) continue;
      picked.push_back(index);
      for (int col : available) taken[col] = stamp;
      if (static_cast<int>(picked.size()) > remaining) {
        ++leaves;
        emit({4, static_cast<int>(picked.size())});
        for (int i : picked) emit({pool[i].first, pool[i].second + 1});
        return true;
      }
    }
  }
  return false;
}

bool exclude(int remaining) {
  ++nodes;
  for (int r : stabilizers[selected.back()]) if (overlaps[r] > 6) {
    ++leaves;
    emit({3, r});
    return true;
  }
  if (odds.empty()) {
    for (int col : selected) std::cerr << ' ' << col;
    std::cerr << '\n';
    return false;
  }
  std::array<std::vector<int>, 13> buckets;
  for (int row : odds) {
    int width = 0;
    for (int col : neighbors[row]) width += !marked[col];
    if (width == 0) { ++leaves; emit({0, row}); return true; }
    buckets[width].push_back(row);
  }
  fresh_stamp();
  std::vector<int> packing;
  int branch = -1;
  for (int width = 1; width <= 12; ++width) {
    for (int row : buckets[width]) {
      if (branch < 0) branch = row;
      bool disjoint = true;
      for (int col : neighbors[row]) {
        if (!marked[col] && taken[col] == stamp) { disjoint = false; break; }
      }
      if (!disjoint) continue;
      for (int col : neighbors[row]) if (!marked[col]) taken[col] = stamp;
      packing.push_back(row);
      if (static_cast<int>(packing.size()) > remaining) {
        emit_packing(packing);
        return true;
      }
    }
  }
  packing.clear();
  if (strong_packing(remaining, packing)) {
    emit_packing(packing);
    return true;
  }
  if (useXorPacking && xor_packing(remaining)) return true;
  std::array<std::vector<int>, 4> candidates;
  for (int col : neighbors[branch]) if (!marked[col]) {
    int score = 0;
    for (int row : checks[col]) score += odd[row];
    candidates[score].push_back(col);
  }
  // A satisfying extension must select one available neighbour of the odd row.
  // A failed selection is kept marked while the next child is explored.
  for (int score = 3; score >= 1; --score) {
    for (int col : candidates[score]) {
      emit({2, col});
      marked[col] = true;
      selected.push_back(col);
      toggle(col);
      for (int r : stabilizers[col]) ++overlaps[r];
      if (!exclude(remaining - 1)) return false;
      for (int r : stabilizers[col]) --overlaps[r];
      toggle(col);
      selected.pop_back();
    }
  }
  emit({0, branch});
  for (const auto& bucket : candidates) for (int col : bucket) marked[col] = false;
  return true;
}

int main(int argc, char** argv) {
  if (argc < 8 || argc > 10) {
    std::cerr << "usage: search_reduced OPPOSITE STABILIZERS STATIONS CHANNELS BUDGET BEGIN END [--count|--binary] [--xor]\n";
    return 2;
  }
  int stations = std::stoi(argv[3]), channels = std::stoi(argv[4]);
  if (stations < 1 || channels < 1 || 1LL * stations * channels > cols / 12) return 2;
  int cell = stations * channels;
  int n = 12 * cell, m = 3 * cell;
  int bound = std::stoi(argv[5]), start = std::stoi(argv[6]), end = std::stoi(argv[7]);
  std::string mode;
  for (int i = 8; i < argc; ++i) {
    const std::string option = argv[i];
    if (option == "--xor" && !useXorPacking) useXorPacking = true;
    else if ((option == "--count" || option == "--binary") && mode.empty()) mode = option;
    else return 2;
  }
  outputWords = mode != "--count";
  binaryWords = mode == "--binary";
  if (bound < 1 || bound > 14 || start < 0 || start >= end || end > 12 * channels) return 2;
  std::ifstream input(argv[1]), stab(argv[2]);
  std::array<int, cols> weight{}, stabWeight{};
  for (int row = 0; row < m; ++row) {
    for (int& col : neighbors[row]) {
      if (!(input >> col) || col < 0 || col >= n || weight[col] == 3) return 2;
      checks[col][weight[col]++] = row;
    }
    for (int k = 0; k < 12; ++k) {
      int col;
      if (!(stab >> col) || col < 0 || col >= n || stabWeight[col] == 3) return 2;
      stabilizers[col][stabWeight[col]++] = row;
    }
  }
  input >> std::ws;
  stab >> std::ws;
  if (!input.eof() || !stab.eof()) return 2;
  for (int c = 0; c < n; ++c) if (weight[c] != 3 || stabWeight[c] != 3) return 2;
  for (int anchor = start; anchor < end; ++anchor) {
    for (int c = 0; c < n; ++c) {
      marked[c] = (c / cell) * channels + c % channels < anchor;
    }
    int col = (anchor / channels) * cell + anchor % channels;
    selected.push_back(col);
    marked[col] = true;
    toggle(col);
    for (int r : stabilizers[col]) ++overlaps[r];
    nodes = leaves = wordCount = 0;
    words.clear();
    if (!exclude(bound - 1)) {
      std::cerr << "reduced zero-syndrome support at anchor " << anchor << '\n';
      return 1;
    }
    std::cerr << anchor << ' ' << nodes << ' ' << leaves << ' ' << wordCount << std::endl;
    if (binaryWords) {
      static_assert(std::endian::native == std::endian::little);
      std::cout.write(reinterpret_cast<const char*>(&wordCount), sizeof(wordCount));
      std::cout.write(reinterpret_cast<const char*>(words.data()), words.size() * sizeof(words[0]));
    } else if (outputWords) {
      for (int word : words) std::cout << word << ' ';
      std::cout << '\n';
    }
    for (int r : stabilizers[col]) --overlaps[r];
    toggle(col);
    marked[col] = false;
    selected.pop_back();
  }
  return std::cout ? 0 : 2;
}

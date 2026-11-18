// Generate untrusted reduced-support exclusion programs for routed Armillary codes.
// Opcode 3 records a stabilizer row intersecting the current support more than six times.
// Each stdout line contains one complete program in anchor order.

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

constexpr int rows = 2172;
constexpr int cols = 8688;
std::array<std::array<int, 3>, cols> stabilizers{};
std::array<int, rows> overlaps{};
bool outputWords = true;
bool binaryWords = false;
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
  if (++stamp == 0) {
    taken.fill(0);
    ++stamp;
  }
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
  if (argc != 8 && argc != 9) {
    std::cerr << "usage: search_reduced OPPOSITE STABILIZERS STATIONS CHANNELS BUDGET BEGIN END [--count|--binary]\n";
    return 2;
  }
  int stations = std::stoi(argv[3]), channels = std::stoi(argv[4]);
  if (stations < 1 || channels < 1 || 1LL * stations * channels > cols / 12) return 2;
  int cell = stations * channels;
  int n = 12 * cell, m = 3 * cell;
  int bound = std::stoi(argv[5]), start = std::stoi(argv[6]), end = std::stoi(argv[7]);
  const std::string mode = argc == 9 ? argv[8] : "";
  outputWords = mode != "--count";
  binaryWords = mode == "--binary";
  if (bound < 1 || bound > 14 || start < 0 || start >= end || end > 12 * channels ||
      (!mode.empty() && mode != "--count" && mode != "--binary")) return 2;
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

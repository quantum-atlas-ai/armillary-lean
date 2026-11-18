// Generate untrusted exclusion-program words for the frozen 8749 instance.
// Usage: search8749 ROWS BUDGET BEGIN_ANCHOR END_ANCHOR
// Each stdout line contains one complete program in anchor order.

#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

constexpr int rows = 909;
constexpr int cols = 3636;
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
std::vector<int> words;

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

bool exclude(int remaining) {
  ++nodes;
  if (odds.empty()) {
    for (int col : selected) std::cerr << ' ' << col;
    std::cerr << '\n';
    return false;
  }
  std::array<std::vector<int>, 13> buckets;
  for (int row : odds) {
    int width = 0;
    for (int col : neighbors[row]) width += !marked[col];
    if (width == 0) { ++leaves; words.insert(words.end(), {0, row}); return true; }
    buckets[width].push_back(row);
  }
  ++stamp;
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
        ++leaves;
        words.insert(words.end(), {1, static_cast<int>(packing.size())});
        words.insert(words.end(), packing.begin(), packing.end());
        return true;
      }
    }
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
      words.insert(words.end(), {2, col});
      marked[col] = true;
      selected.push_back(col);
      toggle(col);
      if (!exclude(remaining - 1)) return false;
      toggle(col);
      selected.pop_back();
    }
  }
  words.insert(words.end(), {0, branch});
  for (const auto& bucket : candidates) for (int col : bucket) marked[col] = false;
  return true;
}

int main(int argc, char** argv) {
  if (argc != 5) {
    std::cerr << "usage: search8749 ROWS BUDGET BEGIN_ANCHOR END_ANCHOR\n";
    return 2;
  }
  std::ifstream input(argv[1]);
  std::array<int, cols> weight{};
  for (int row = 0; row < rows; ++row) for (int& col : neighbors[row]) {
    if (!(input >> col) || col < 0 || col >= cols || weight[col] == 3) return 2;
    checks[col][weight[col]++] = row;
  }
  if (std::any_of(weight.begin(), weight.end(), [](int w) { return w != 3; })) return 2;
  int bound = std::stoi(argv[2]);
  int start = std::stoi(argv[3]), end = std::stoi(argv[4]);
  if (bound < 1 || bound > 10 || start < 0 || start >= end || end > 36) return 2;
  for (int anchor = start; anchor < end; ++anchor) {
    int col = (anchor / 3) * 303 + (anchor % 3);
    selected.push_back(col);
    marked[col] = true;
    toggle(col);
    nodes = leaves = 0;
    words.clear();
    if (!exclude(bound - 1)) return 1;
    std::cerr << anchor << ' ' << nodes << ' ' << leaves << ' ' << words.size() << std::endl;
    for (int word : words) std::cout << word << ' ';
    std::cout << '\n';
    toggle(col);
    marked[col] = false;
    selected.pop_back();
  }
}

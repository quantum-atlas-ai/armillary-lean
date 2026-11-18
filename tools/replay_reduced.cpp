// Independently replay packed reduced certificate streams against exported rows.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <span>
#include <string>
#include <vector>

using Row = std::array<int, 12>;

bool read_rows(const char* path, int cell, std::vector<Row>& rows) {
  std::ifstream file(path);
  for (Row& row : rows) {
    for (int block = 0; block < 12; ++block) {
      int c;
      if (!(file >> c) || c < 0 || c / cell != block) return false;
      row[block] = c;
    }
  }
  file >> std::ws;
  return file.eof();
}

struct Replay {
  const std::vector<Row>& checks;
  const std::vector<Row>& stabilizers;
  std::vector<uint16_t> words;
  std::vector<bool> selected, marked;
  std::vector<uint32_t> column_stamp, row_stamp;
  uint32_t stamp = 0;
  size_t at = 0;
  int weight = 1;
  int budget;

  Replay(const std::vector<Row>& checks, const std::vector<Row>& stabilizers, int columns, int bound)
      : checks(checks), stabilizers(stabilizers), selected(columns), marked(columns),
        column_stamp(columns), row_stamp(checks.size()), budget(bound) {}

  int count(const Row& row) const {
    int result = 0;
    for (int c : row) result += selected[c];
    return result;
  }

  void fresh_stamp() {
    if (++stamp == 0) {
      std::fill(column_stamp.begin(), column_stamp.end(), 0);
      std::fill(row_stamp.begin(), row_stamp.end(), 0);
      ++stamp;
    }
  }

  template <typename Columns>
  bool add_available(const Columns& columns) {
    for (int col : columns) {
      if (marked[col]) continue;
      if (column_stamp[col] == stamp) return false;
      column_stamp[col] = stamp;
    }
    return true;
  }

  bool packing(int size, bool allow_xor) {
    if (weight + size <= budget) return false;
    fresh_stamp();
    for (int i = 0; i < size; ++i) {
      const int row = next();
      if (row < 0 || row >= static_cast<int>(checks.size())) return false;
      if (!allow_xor) {
        if (row_stamp[row] == stamp) return false;
        row_stamp[row] = stamp;
      }
      const int second = allow_xor ? next() : 0;
      if (second < 0 || second > static_cast<int>(checks.size())) return false;
      if (second == 0) {
        if (count(checks[row]) % 2 != 1 || !add_available(checks[row])) return false;
      } else {
        const auto& first_row = checks[row];
        const auto& second_row = checks[second - 1];
        if ((count(first_row) + count(second_row)) % 2 != 1) return false;
        std::array<int, 24> difference;
        const auto end = std::set_symmetric_difference(
            first_row.begin(), first_row.end(), second_row.begin(), second_row.end(),
            difference.begin());
        if (!add_available(std::span(difference.begin(), end))) return false;
      }
    }
    return true;
  }

  int next() { return at < words.size() ? words[at++] : -1; }

  bool tree(int fuel) {
    if (!fuel) return false;
    const int tag = next();
    const int arg = next();
    if (arg < 0) return false;
    switch (tag) {
      case 0:
        return arg < static_cast<int>(checks.size()) && count(checks[arg]) % 2 == 1 &&
            std::all_of(checks[arg].begin(), checks[arg].end(), [&](int c) { return marked[c]; });
      case 1:
        return arg <= static_cast<int>(checks.size()) && packing(arg, false);
      case 2: {
        if (arg >= static_cast<int>(marked.size()) || marked[arg]) return false;
        marked[arg] = selected[arg] = true;
        ++weight;
        const bool yes = tree(fuel - 1);
        --weight;
        selected[arg] = false;
        const bool no = yes && tree(fuel - 1);
        marked[arg] = false;
        return no;
      }
      case 3:
        return arg < static_cast<int>(stabilizers.size()) && count(stabilizers[arg]) > 6;
      case 4:
        return packing(arg, true);
      default:
        return false;
    }
  }

  bool anchor(int i, int q, int cell) {
    const int anchor = (i / q) * cell + i % q;
    std::fill(selected.begin(), selected.end(), false);
    for (int c = 0; c < static_cast<int>(marked.size()); ++c) {
      marked[c] = (c / cell) * q + c % q < i;
    }
    marked[anchor] = selected[anchor] = true;
    weight = 1;
    at = 0;
    return tree(256) && at == words.size();
  }
};

int main(int argc, char** argv) {
  if (argc != 9) {
    std::cerr << "usage: replay_reduced OPPOSITE STABILIZERS STATIONS CHANNELS BUDGET BEGIN END BINARY\n";
    return 2;
  }
  static_assert(std::endian::native == std::endian::little);
  const int p = std::stoi(argv[3]), q = std::stoi(argv[4]), bound = std::stoi(argv[5]);
  const int first = std::stoi(argv[6]), last = std::stoi(argv[7]);
  if (p < 1 || q < 1 || 1LL * p * q * 12 > 16384 || bound < 1 || bound > 14 ||
      first < 0 || first >= last || last > 12 * q) return 2;
  const int cell = p * q;
  std::vector<Row> checks(3 * cell), stabilizers(3 * cell);
  if (!read_rows(argv[1], cell, checks) || !read_rows(argv[2], cell, stabilizers)) return 2;
  std::ifstream file(argv[8], std::ios::binary | std::ios::ate);
  const auto size = file.tellg();
  if (size < 0) return 2;
  file.seekg(0);
  Replay state(checks, stabilizers, 12 * cell, bound);
  for (int i = first; i < last; ++i) {
    uint64_t n = 0;
    if (!file.read(reinterpret_cast<char*>(&n), sizeof(n)) || n == 0 ||
        n > static_cast<uint64_t>(size - file.tellg()) / sizeof(uint16_t)) return 2;
    state.words.resize(n);
    if (!file.read(reinterpret_cast<char*>(state.words.data()), n * sizeof(uint16_t))) return 2;
    if (!state.anchor(i, q, cell)) {
      std::cerr << "invalid anchor " << i << " at word " << state.at << '\n';
      return 1;
    }
    std::cout << "verified " << i << " (" << n << " words)" << std::endl;
  }
  return file.peek() == std::char_traits<char>::eof() ? 0 : 2;
}

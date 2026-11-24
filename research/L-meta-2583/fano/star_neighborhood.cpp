// Exact one-deletion, one-gate-replacement neighborhood of the 27-gate Fano star.
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

using Word = std::uint64_t;
struct Gate { bool conjunction; int a, b; };

bool incident(int p, int l) {
    const int r = (p + l) % 7;
    return r == 0 || r == 1 || r == 3;
}

bool target(int row) {
    for (int p = 0; p < 7; ++p)
        for (int l = 0; l < 7; ++l)
            if (incident(p,l) && (row & (1 << p)) && (row & (1 << (7+l)))) return true;
    return false;
}

std::vector<Gate> stars() {
    std::vector<Gate> gates;
    std::vector<int> roots;
    for (int p = 0; p < 7; ++p) {
        std::vector<int> lines;
        for (int l = 0; l < 7; ++l)
            if (incident(p,l)) lines.push_back(7+l);
        const int w = 14 + static_cast<int>(gates.size());
        gates.push_back({false,lines[0],lines[1]});
        gates.push_back({false,w,lines[2]});
        gates.push_back({true,p,w+1});
        roots.push_back(w+2);
    }
    int out = roots[0];
    for (int i = 1; i < 7; ++i) {
        gates.push_back({false,out,roots[i]});
        out = 13 + static_cast<int>(gates.size());
    }
    return gates;
}

int main() {
    const auto gates = stars();
    std::vector<int> rows;
    for (int p = 0; p < 7; ++p)
        for (int l = 0; l < 7; ++l)
            if (incident(p,l)) rows.push_back((1 << p) | (1 << (7+l)));
    const Word expected = (Word{1} << rows.size()) - 1;
    for (int row = 0; row < (1 << 14); ++row) {
        if (target(row)) continue;
        bool maximal = true;
        for (int i = 0; i < 14; ++i)
            if (!(row & (1 << i)) && !target(row | (1 << i))) maximal = false;
        if (maximal) rows.push_back(row);
    }
    if (gates.size() != 27 || rows.size() != 58) return 2;
    std::array<Word, 41> wires{};
    for (int i = 0; i < 14; ++i)
        for (std::size_t j = 0; j < rows.size(); ++j)
            if (rows[j] & (1 << i)) wires[i] |= Word{1} << j;
    auto recompute = [&](int index) {
        const Gate& g = gates[index];
        return g.conjunction ? (wires[g.a] & wires[g.b]) : (wires[g.a] | wires[g.b]);
    };
    for (int i = 0; i < 27; ++i) wires[14+i] = recompute(i);
    if (wires[40] != expected) return 2;

    std::uint64_t count = 0;
    for (int removed = 0; removed < 27; ++removed) {
        for (int alias = 0; alias < 14+removed; ++alias) {
            for (int edited = 0; edited < 27; ++edited) {
                if (edited == removed) continue;
                for (int k = 0; k < edited; ++k)
                    wires[14+k] = k == removed ? wires[alias] : recompute(k);
                for (int a = 0; a < 14+edited; ++a) {
                    if (a == 14+removed) continue;
                    for (int b = a; b < 14+edited; ++b) {
                        if (b == 14+removed) continue;
                        for (int op = 0; op < 2; ++op) {
                            wires[14+edited] = op ? (wires[a] & wires[b]) : (wires[a] | wires[b]);
                            for (int k = edited+1; k < 27; ++k)
                                wires[14+k] = k == removed ? wires[alias] : recompute(k);
                            ++count;
                            if (wires[40] == expected) {
                                std::cout << "match: removed " << removed << ", alias " << alias
                                          << ", edited " << edited << ", inputs " << a << ' ' << b
                                          << ", AND " << op << '\n';
                                return 1;
                            }
                        }
                    }
                }
            }
        }
    }
    std::cout << count << " parameter choices; no match on the 58 complete boundary rows\n";
}

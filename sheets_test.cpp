#include "sheets.hpp"
#include <array>
#include <cstdio>
#include <cstdlib>
#include <format>
#include <iomanip>
#include <optional>
#include <print>
#include <utility>
#include <vector>

template <class... Ts> struct overload : Ts... {
  using Ts::operator()...;
};

extern "C" int init_spec(void);
extern "C" void run_lean(uint8_t const *input, size_t length, char **output);

struct Parser {
  std::span<std::uint8_t> data;
  std::size_t pos;

  std::optional<std::uint8_t> read_byte() {
    if (pos >= data.size())
      return {};
    return data[pos++];
  }

  std::optional<std::uint32_t> read_nat32() {
    std::array<std::uint32_t, 4> bs{};

    for (std::size_t i = 0; i < 4; ++i) {
      auto b = read_byte();
      if (!b)
        return {};
      bs[i] = *b;
    }

    return bs[0] | (bs[1] << 8) | (bs[2] << 16) | (bs[3] << 24);
  }

  std::optional<double> read_float64() {
    std::array<std::uint64_t, 8> bs{};

    for (std::size_t i = 0; i < 8; ++i) {
      auto b = read_byte();
      if (!b)
        return {};
      bs[i] = *b;
    }

    std::uint64_t u = bs[0] | (bs[1] << 8) | (bs[2] << 16) | (bs[3] << 24) |
                      (bs[4] << 32) | (bs[5] << 40) | (bs[6] << 48) |
                      (bs[7] << 56);

    return std::bit_cast<double>(u);
  }

  std::optional<Expr> parse_expr() {
    auto tag = read_byte();
    if (!tag)
      return {};

    switch (*tag % 8) {
    case 1: {
      auto val = read_float64();
      if (!val)
        return {};
      return Expr{Atomic{*val}};
    } break;
    case 2: {
      return Expr{Atomic{"Hello"}};
    } break;
    case 3: {
      return Expr{Atomic{None{}}};
    } break;
    case 4: {
      auto r = read_nat32();
      auto c = read_nat32();
      if (!(r && c))
        return {};
      return Expr{CellId{*r, *c}};
    } break;
    case 5: {
      auto e1 = parse_expr();
      auto e2 = parse_expr();
      if (!(e1 && e2))
        return {};
      return Expr{Add{std::make_unique<Expr>(std::move(*e1)),
                      std::make_unique<Expr>(std::move(*e2))}};
    } break;
    case 6: {
      auto e1 = parse_expr();
      auto e2 = parse_expr();
      if (!(e1 && e2))
        return {};
      return Expr{Sub{std::make_unique<Expr>(std::move(*e1)),
                      std::make_unique<Expr>(std::move(*e2))}};
    } break;
    case 7: {
      auto e1 = parse_expr();
      auto e2 = parse_expr();
      if (!(e1 && e2))
        return {};
      return Expr{Mult{std::make_unique<Expr>(std::move(*e1)),
                       std::make_unique<Expr>(std::move(*e2))}};
    } break;
    case 0: {
      auto e1 = parse_expr();
      auto e2 = parse_expr();
      if (!(e1 && e2))
        return {};
      return Expr{Div{std::make_unique<Expr>(std::move(*e1)),
                      std::make_unique<Expr>(std::move(*e2))}};
    } break;
    default:
      std::unreachable();
    }
  }

  bool parse_and_run(Grid &grid) {
    while (pos < data.size()) {
      auto op = read_byte();
      if (!op)
        return false;
      switch (*op % 3) {
      case 1: {
        auto r = read_nat32();
        auto c = read_nat32();
        auto ex = parse_expr();
        if (!(r && c && ex))
          return false;
        grid.set({*r, *c}, std::move(*ex));
      } break;
      case 2: {
        auto r = read_nat32();
        auto c = read_nat32();
        if (!(r && c))
          return false;
        grid.erase({*r, *c});
      } break;
      case 0: {
        grid.evaluate();
      } break;
      default:
        std::unreachable();
      }
    }

    return true;
  }
};

std::string atom_repr(Atomic const &a) {
  return std::visit(overload{
                        [](double const &n) { return std::format("N:{}", n); },
                        [](std::string const &s) {
                          std::stringstream ss;
                          ss << std::quoted(s);
                          return std::format("S:{}", ss.str());
                        },
                        [](None const &) { return std::string{"Z"}; },
                        [](Error const &e) {
                          switch (e) {
                          case Error::DivByZero:
                            return std::string{"E:div0"};
                          case Error::TypeMismatch:
                            return std::string{"E:type"};
                          case Error::Cyclic:
                            return std::string{"E:cycle"};
                          default:
                            std::unreachable();
                          }
                        },
                    },
                    a.data);
}

std::string atom_grid_repr(std::map<CellId, Atomic> const &m) {
  std::string res{};
  bool is_first{true};
  for (auto const &[k, v] : m) {
    if (is_first) {
      is_first = false;
      res += std::format("{},{}={}", k.row, k.col, atom_repr(v));
    } else {
      res += std::format(";{},{}={}", k.row, k.col, atom_repr(v));
    }
  }
  return res;
}

std::string run_impl(std::span<std::uint8_t> inp) {
  Grid g{};
  if (Parser{inp, 0}.parse_and_run(g)) {
    Evaluation ev{{}, g.cells};
    ev.resolve_all();
    return atom_grid_repr(ev.ctx);
  } else {
    return "ERROR";
  }
}

int main(void) {
  init_spec();

  uint8_t input[] = {
      1, // Set ⟨2, 1⟩ (atom (number 3.125))
      2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 9,  64,

      1, // Set ⟨2, 2⟩ (atom (number 8.0))
      2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 32, 64,

      1, // Set ⟨3, 1⟩ (add (ref ⟨2, 1⟩) (ref ⟨2, 2⟩))
      3, 0, 0, 0, 1, 0, 0, 0, 7, 4, 2, 0, 0, 0, 1, 0,  0,
      0, 4, 2, 0, 0, 0, 2, 0, 0, 0,

      1,
      3, 0, 0, 0, 2, 0, 0, 0, 2,

      3 // Evaluate
  };

  char *out;
  run_lean(input, sizeof(input), &out);
  std::puts(out);

  std::free(out);

  auto s =
      run_impl(std::span{static_cast<std::uint8_t *>(input), sizeof(input)});
  std::println("{}", s);

  return 0;
}

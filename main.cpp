#include "sheets.hpp"
#include <iomanip>
#include <print>
#include <readline/history.h>
#include <readline/readline.h>
#include <sstream>
#include <utility>

template <class... Ts> struct overload : Ts... {
  using Ts::operator()...;
};

std::optional<CellId> parse_cell_id(std::string_view s) {
  if (s.empty())
    return std::nullopt;

  std::size_t i = 0;
  while (i < s.size() && std::isalpha(static_cast<unsigned char>(s[i]))) {
    i++;
  }

  if (i == 0 || i == s.size())
    return std::nullopt;

  std::uint32_t col = 0;
  for (std::size_t j = 0; j < i; ++j) {
    char ch = std::toupper(static_cast<unsigned char>(s[j]));
    col = col * 26 + (ch - 'A' + 1);
  }

  col -= 1;

  std::uint32_t row = 0;
  for (std::size_t j = i; j < s.size(); ++j) {
    if (!std::isdigit(static_cast<unsigned char>(s[j])))
      return std::nullopt;
    row = row * 10 + (s[j] - '0');
  }

  if (row == 0)
    return std::nullopt;

  row -= 1;

  return CellId{row, col};
}

std::string format_cell_id(CellId id) {
  std::string col_str;
  std::uint32_t col = id.col + 1;
  while (col > 0) {
    std::uint32_t rem = (col - 1) % 26;
    col_str.push_back(static_cast<char>('A' + rem));
    col = (col - 1) / 26;
  }
  std::reverse(col_str.begin(), col_str.end());
  return col_str + std::to_string(id.row + 1);
}

struct Token {
  enum class Kind {
    Number,
    String,
    Cell,
    Plus,
    Minus,
    Mul,
    Div,
    LParen,
    RParen,
    End
  } kind;

  std::string text;

  double num{0.0};
};

enum class LexerError { UnclosedString, UnrecognisedChar };

struct Lexer {
  std::string_view src;
  std::size_t pos{0};

  Token next() {
    while (pos < src.size() &&
           std::isspace(static_cast<unsigned char>(src[pos]))) {
      pos++;
    }
    if (pos >= src.size())
      return {Token::Kind::End, ""};

    char c = src[pos];

    switch (c) {
    case '+': {
      pos++;
      return {Token::Kind::Plus, "+"};
    } break;
    case '-': {
      pos++;
      return {Token::Kind::Minus, "-"};
    } break;
    case '*': {
      pos++;
      return {Token::Kind::Mul, "*"};
    } break;
    case '/': {
      pos++;
      return {Token::Kind::Div, "/"};
    } break;
    case '(': {
      pos++;
      return {Token::Kind::LParen, "("};
    } break;
    case ')': {
      pos++;
      return {Token::Kind::RParen, ")"};
    } break;
    default:
      break;
    }

    if (c == '"') {
      pos++;
      std::string val;
      while (pos < src.size()) {
        if (src[pos] == '"') {
          pos++;
          return {Token::Kind::String, val};
        }
        val += src[pos++];
      }
      throw LexerError::UnclosedString;
    }

    if (std::isdigit(static_cast<unsigned char>(c)) || c == '.') {
      std::size_t start = pos;
      while (pos < src.size() &&
             (std::isdigit(static_cast<unsigned char>(src[pos])) ||
              src[pos] == '.')) {
        pos++;
      }
      std::string num_str(src.substr(start, pos - start));
      return {Token::Kind::Number, num_str, std::stod(num_str)};
    }

    if (std::isalpha(static_cast<unsigned char>(c))) {
      std::size_t start = pos;
      while (pos < src.size() &&
             std::isalnum(static_cast<unsigned char>(src[pos]))) {
        pos++;
      }
      return {Token::Kind::Cell, std::string(src.substr(start, pos - start))};
    }

    throw LexerError::UnrecognisedChar;
  }
};

struct Parser {
  Lexer lexer;
  Token current;

  void advance() { current = lexer.next(); }

  explicit Parser(std::string_view inp) : lexer{inp} { advance(); }

  std::optional<Expr> parse() {
    auto res = parse_expr();
    if (!res || current.kind != Token::Kind::End)
      return std::nullopt;
    return res;
  }

  std::optional<Expr> parse_expr() {
    auto left = parse_term();
    if (!left)
      return std::nullopt;

    while (current.kind == Token::Kind::Plus ||
           current.kind == Token::Kind::Minus) {
      auto op = current.kind;
      advance();
      auto right = parse_term();
      if (!right)
        return std::nullopt;

      Expr parent;
      if (op == Token::Kind::Plus) {
        parent.data =
            Add{std::make_shared<Expr>(*left), std::make_shared<Expr>(*right)};
      } else {
        parent.data =
            Sub{std::make_shared<Expr>(*left), std::make_shared<Expr>(*right)};
      }
      left = parent;
    }
    return left;
  }

  std::optional<Expr> parse_term() {
    auto left = parse_factor();
    if (!left)
      return std::nullopt;

    while (current.kind == Token::Kind::Mul ||
           current.kind == Token::Kind::Div) {
      auto op = current.kind;
      advance();
      auto right = parse_factor();
      if (!right)
        return std::nullopt;

      Expr parent;
      if (op == Token::Kind::Mul) {
        parent.data =
            Mult{std::make_shared<Expr>(*left), std::make_shared<Expr>(*right)};
      } else {
        parent.data =
            Div{std::make_shared<Expr>(*left), std::make_shared<Expr>(*right)};
      }
      left = parent;
    }
    return left;
  }

  std::optional<Expr> parse_factor() {
    if (current.kind == Token::Kind::Number) {
      Atomic a;
      a.data = current.num;
      advance();
      return Expr{.data = a};
    }
    if (current.kind == Token::Kind::String) {
      Atomic a;
      a.data = current.text;
      advance();
      return Expr{.data = a};
    }
    if (current.kind == Token::Kind::Cell) {
      auto cell = parse_cell_id(current.text);
      if (!cell)
        return std::nullopt;
      advance();
      return Expr{.data = *cell};
    }
    if (current.kind == Token::Kind::LParen) {
      advance();
      auto e = parse_expr();
      if (current.kind != Token::Kind::RParen)
        return std::nullopt;
      advance();
      return e;
    }
    return std::nullopt;
  }
};

std::string format_atom(Atomic const &atom) {
  return std::visit(overload{[](double const &v) { return std::to_string(v); },
                             [](std::string const &s) {
                               std::stringstream ss;
                               ss << std::quoted(s);
                               return ss.str();
                             },
                             [](None const &) -> std::string { return "None"; },
                             [](Error const &err) -> std::string {
                               switch (err) {
                               case Error::DivByZero:
                                 return "#DIV0!";
                               case Error::TypeMismatch:
                                 return "#TYPE!";
                               case Error::Cyclic:
                                 return "#CYCLE!";
                               case Error::InvalidNumber:
                                 return "#INVNUM!";
                               default:
                                 std::unreachable();
                               }
                             }},
                    atom.data);
}

std::string format_expr(Expr const &expr) {
  return std::visit(overload{
                        [](Atomic const &atom) { return format_atom(atom); },
                        [](CellId const &cell) { return format_cell_id(cell); },
                        [](Add const &ex) {
                          return "(" + format_expr(*ex.left) + " + " +
                                 format_expr(*ex.right) + ")";
                        },
                        [](Sub const &ex) {
                          return "(" + format_expr(*ex.left) + " - " +
                                 format_expr(*ex.right) + ")";
                        },
                        [](Mult const &ex) {
                          return "(" + format_expr(*ex.left) + " * " +
                                 format_expr(*ex.right) + ")";
                        },
                        [](Div const &ex) {
                          return "(" + format_expr(*ex.left) + " / " +
                                 format_expr(*ex.right) + ")";
                        },
                    },
                    expr.data);
}

int main() {
  std::println("Type 'help' to list all commands");

  Grid grid{};

  while (true) {
    char *buf = readline(">>> ");
    if (!buf) {
      std::println("Exiting...");
      break;
    }

    std::string input{buf};
    std::free(buf);

    if (!input.empty()) {
      add_history(input.c_str());
    }

    if (input == "help") {
      std::println("Commands:");
      std::println("  <cell> := <expr>   Assign an expression to a cell (e.g. A1 := A2 + B1 * 2)");
      std::println("  delete <cell>      Delete expression at cell (e.g. delete A1)");
      std::println("  list               List occupied cells, expressions, and evaluation results");
      continue;
    }

    if (input == "list") {
      if (grid.cells.empty()) {
        std::println("Grid is empty");
        continue;
      }

      Grid results{grid};
      results.evaluate();

      std::println("{:<8} {:<25} {:<15}", "Cell", "Expression", "Value");
      std::println("--------------------------------------------------");

      for (auto const &[cell_id, expr] : grid.cells) {
        std::string cell_str = format_cell_id(cell_id);
        std::string expr_str = format_expr(expr);

        std::string val_str =
            format_atom(std::get<Atomic>(results.cells.at(cell_id).data));

        std::println("{:<8} {:<25} {:<15}", cell_str, expr_str, val_str);
      }
      continue;
    }

    if (input.starts_with("delete ")) {
      std::string cell_str = input.substr(7);

      cell_str.erase(0, cell_str.find_first_not_of(" \t"));
      cell_str.erase(cell_str.find_last_not_of(" \t") + 1);

      auto cell_id = parse_cell_id(cell_str);
      if (!cell_id) {
        std::println("Error: Not a valid cell position: '{}'", cell_str);
        continue;
      }

      if (grid.cells.contains(*cell_id)) {
        grid.erase(*cell_id);
        std::println("Deleted {}", format_cell_id(*cell_id));
      } else {
        std::println("Cell {} was not set", format_cell_id(*cell_id));
      }
      continue;
    }

    auto assign_pos = input.find(":=");
    if (assign_pos != input.npos) {
      std::string lhs = input.substr(0, assign_pos);
      std::string rhs = input.substr(assign_pos + 2);

      lhs.erase(0, lhs.find_first_not_of(" \t"));
      lhs.erase(lhs.find_last_not_of(" \t") + 1);

      auto cell = parse_cell_id(lhs);
      if (!cell) {
        std::println("Error: Not a valid cell position: '{}'", lhs);
        continue;
      }

      Parser parser{rhs};
      try {
        auto expr = parser.parse_expr();

        if (!expr) {
          std::println("Error: Failed to parse expression '{}'", rhs);
          continue;
        }

        std::println("Set {} to {}", format_cell_id(*cell), format_expr(*expr));
        grid.set(*cell, std::move(*expr));
      } catch (LexerError err) {
        switch (err) {
        case LexerError::UnclosedString:
          std::println("Unclosed string literal");
          break;
        case LexerError::UnrecognisedChar:
          std::println("Unrecognised token or character");
          break;
        default:
          std::unreachable();
        }
        continue;
      }
    }
  }
}

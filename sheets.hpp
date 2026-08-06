#pragma once
#include <compare>
#include <cstdint>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <map>
#include <variant>

struct CellId {
  std::uint32_t row;
  std::uint32_t col;

  auto operator<=>(const CellId &b) const = default;
};

enum class Error {
  DivByZero,
  TypeMismatch,
  Cyclic
};

struct None{};

struct Atomic {
  using Variant = std::variant<double, std::string, None, Error>;
  Variant data;

  std::optional<double> num_value() const;
  Atomic operator+(Atomic const &other) const;
  Atomic operator-(Atomic const &other) const;
  Atomic operator*(Atomic const &other) const;
  Atomic operator/(Atomic const &other) const;
};

struct Expr;

struct Add { std::shared_ptr<Expr> left, right; };
struct Sub { std::shared_ptr<Expr> left, right; };
struct Mult { std::shared_ptr<Expr> left, right; };
struct Div { std::shared_ptr<Expr> left, right; };

using Context = std::map<CellId, Atomic>;

struct Expr {
  using Variant = std::variant<Atomic, CellId, Add, Sub, Mult, Div>;
  Variant data;

  std::set<CellId> deps() const;
  Atomic eval_with(Context const &ctx) const;
  bool is_free(Context const &ctx) const;
};

struct Grid {
  std::map<CellId, Expr> cells;

  void set(CellId cell, Expr &&ex);
  void erase(CellId cell);
  void evaluate();
};

struct Evaluation {
  Context ctx;
  std::map<CellId, Expr> remain;

  std::optional<CellId> find_free() const;
  std::optional<std::pair<CellId, Atomic>> compute_one() const;
  void step(std::pair<CellId, Atomic> comp);
  void resolve_all();
};

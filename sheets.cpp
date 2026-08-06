#include "sheets.hpp"
#include <algorithm>
#include <cmath>
#include <optional>
#include <variant>

template <class... Ts> struct overload : Ts... {
  using Ts::operator()...;
};

void Grid::set(CellId cell, Expr &&ex) { cells[cell] = std::move(ex); }

void Grid::erase(CellId cell) { cells.erase(cell); }

std::set<CellId> Expr::deps() const {
  return std::visit(
      overload{[](Atomic const &) -> std::set<CellId> { return {}; },
               [](CellId const &id) -> std::set<CellId> { return {id}; },
               [](auto const &x) -> std::set<CellId> {
                 std::set<CellId> un{x.left->deps()};
                 un.merge(x.right->deps());
                 return un;
               }},
      data);
}

std::optional<double> Atomic::num_value() const {
  return std::visit(
      overload{[](double x) -> std::optional<double> { return x; },
               [](None) -> std::optional<double> { return 0; },
               [](auto) -> std::optional<double> { return {}; }},
      data);
}

Atomic Atomic::canon() const {
  if (std::holds_alternative<double>(data)) {
    if (std::isnan(std::get<double>(data))) {
      return {Error::InvalidNumber};
    }
  }

  return *this;
}

Atomic Atomic::operator+(Atomic const &other) const {
  if (std::holds_alternative<Error>(data)) {
    return *this;
  }

  if (std::holds_alternative<Error>(other.data)) {
    return other;
  }

  if (auto [me, them] =
          std::pair{canon().num_value(), other.canon().num_value()};
      me && them) {
    return {*me + *them};
  } else {
    return {Error::TypeMismatch};
  }
}

Atomic Atomic::operator-(Atomic const &other) const {
  if (std::holds_alternative<Error>(data)) {
    return *this;
  }

  if (std::holds_alternative<Error>(other.data)) {
    return other;
  }

  if (auto [me, them] =
          std::pair{canon().num_value(), other.canon().num_value()};
      me && them) {
    return {*me - *them};
  } else {
    return {Error::TypeMismatch};
  }
}

Atomic Atomic::operator*(Atomic const &other) const {
  if (std::holds_alternative<Error>(data)) {
    return *this;
  }

  if (std::holds_alternative<Error>(other.data)) {
    return other;
  }

  if (auto [me, them] =
          std::pair{canon().num_value(), other.canon().num_value()};
      me && them) {
    return {*me * *them};
  } else {
    return {Error::TypeMismatch};
  }
}

Atomic Atomic::operator/(Atomic const &other) const {
  if (std::holds_alternative<Error>(data)) {
    return *this;
  }

  if (std::holds_alternative<Error>(other.data)) {
    return other;
  }

  if (auto [me, them] =
          std::pair{canon().num_value(), other.canon().num_value()};
      me && them) {
    if (them == 0)
      return {Error::DivByZero};
    return {*me / *them};
  } else {
    return {Error::TypeMismatch};
  }
}

Atomic Expr::eval_with(Context const &ctx) const {
  return std::visit(
      overload{[](Atomic const &a) { return a; },
               [&ctx](CellId const &id) {
                 if (auto it = ctx.find(id); it != ctx.end()) {
                   return it->second;
                 } else {
                   return Atomic{Error::Cyclic};
                 }
               },
               [&ctx](Add const &op) {
                 return op.left->eval_with(ctx) + op.right->eval_with(ctx);
               },
               [&ctx](Sub const &op) {
                 return op.left->eval_with(ctx) - op.right->eval_with(ctx);
               },
               [&ctx](Mult const &op) {
                 return op.left->eval_with(ctx) * op.right->eval_with(ctx);
               },
               [&ctx](Div const &op) {
                 return op.left->eval_with(ctx) / op.right->eval_with(ctx);
               }},
      data);
}

bool Expr::is_free(Context const &ctx) const {
  auto const depSet = deps();
  return std::all_of(depSet.begin(), depSet.end(),
                     [&ctx](CellId id) { return ctx.contains(id); });
}

std::optional<CellId> Evaluation::find_free() const {
  auto iter =
      std::find_if(remain.begin(), remain.end(),
                   [this](auto const &kv) { return kv.second.is_free(ctx); });

  if (iter != remain.end()) {
    return iter->first;
  } else {
    return {};
  }
}

std::optional<std::pair<CellId, Atomic>> Evaluation::compute_one() const {
  if (auto id = find_free(); id) {
    return std::make_pair(*id, remain.at(*id).eval_with(ctx).canon());
  } else {
    if (!remain.empty()) {
      return std::make_pair(remain.begin()->first, Atomic{Error::Cyclic});
    } else {
      return {};
    }
  }
}

void Evaluation::step(std::pair<CellId, Atomic> comp) {
  ctx.emplace(comp);
  remain.erase(comp.first);
}

void Evaluation::resolve_all() {
  for (auto comp = compute_one(); (comp = compute_one());) {
    step(*comp);
  }
}

void Grid::evaluate() {
  Evaluation ev{{}, cells};
  ev.resolve_all();
  cells.clear();
  for (auto const &[k, v] : ev.ctx) {
    cells.emplace(k, Expr{v});
  }
}

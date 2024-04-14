-- Коментарий начинается с `--`

-- Указание Lean писать типы рекурсоров полностью
set_option pp.proofs true

example: ∀α β: Type, α → β → α :=
  λ(α β: Type)(x:α)(_:β) => x

example (α β: Type)(x:α)(_:β): α := x

def f1 (α β: Type)(x:α)(_:β): α := x

#check f1 Nat Nat 3 5
#reduce f1 Nat Nat 3 5
#print f1

#check f1 _ _ 3 5

def f2 {α β: Type}(x:α)(_:β): α := x

#check f2 3 5
#check @f2 Nat Nat 3 5
#check f2 (β := Nat) 3 5

#check λP => ¬P

example {α β: Sort u}(x:α)(_:β): α := x
example (x:α)(_:β): α := x

#print And
#print Or
#print False

example (p:P)(q:Q): P ∧ Q :=
  And.intro p q

example (p:P)(q:Q): P ∧ Q :=
  { left := p, right := q }

example (pq: P ∧ Q): P :=
  let (And.intro p _) := pq
  p

#print And.rec
#print Or.rec
#print False.rec

#check And.intro
#check And.left
#check And.right
#check Or.inl
#check Or.inr
#check Or.elim
#check False.elim

example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp => False.elim (np p)) (λq => q)

example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp => (np p).elim) (λq => q)

example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let (And.intro p qr) := pqr
  qr.elim
    (λq => Or.inl (And.intro p q))
    (λr => Or.inr (And.intro p r))

example {P Q: Prop}(pq: P → Q)(nq: ¬Q): ¬P :=
  λp => nq (pq p : Q)

-- Простые упражнения

example {P Q: Prop}(pq: P ∧ Q): Q ∧ P :=
  sorry
example {P Q R: Prop}(pQr: P ∧ (Q ∧ R)): (P ∧ Q) ∧ R :=
  sorry
example {P Q: Prop}(p: P): Q → P :=
  sorry
example {P Q R: Prop}(pqr: P → Q → R): P ∧ Q → R :=
  sorry
example {P Q R: Prop}(pqr: P → Q → R)(pq: P → Q): P → R :=
  sorry
example {P Q R: Prop}(pq: P → Q)(qr: Q → R): P → R :=
  sorry
example {P Q: Prop}(npq: ¬(P ∨ Q)): ¬P ∧ ¬Q :=
  sorry
example {P Q: Prop}(npQ: ¬P ∨ Q): P → Q :=
  sorry
example {P Q R: Prop}(pQr: P → Q ∧ R): (P → Q) ∧ (P → R) :=
  sorry
example {P Q R: Prop}(pqR: P ∨ Q → R): (P → R) ∧ (Q → R) :=
  sorry

-- Упражнения посложнее

example {P Q R: Prop}(pqR: (P ∨ Q) ∨ R): P ∨ (Q ∨ R) :=
  sorry
example {P Q R: Prop}(pqPr : (P ∧ Q) ∨ (P ∧ R)): P ∧ (Q ∨ R) :=
  sorry
example {P Q R: Prop}(pQr: P ∨ (Q ∧ R)): (P ∨ Q) ∧ (P ∨ R) :=
  sorry

-- Кванторы

#print Exists

example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  And.intro (λx => (apq x).left) (λx => (apq x).right)

example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  ⟨λx => (apq x).left, λx => (apq x).right⟩

example {P: α → β → Prop}(eap: ∃x, ∀y, P x y): ∀y, ∃x, P x y :=
  let ⟨x,ap⟩ := eap
  λy => ⟨x, (ap y : P x y)⟩

#check Exists.intro
#check Exists.elim

-- Простые

example {P: α → β → Prop}(ap: ∀x, ∀y, P x y): ∀y, ∀x, P x y :=
  sorry
example {P: α → β → Prop}(ep: ∃x, ∃y, P x y): ∃y, ∃x, P x y :=
  sorry
example {P: α → Prop}(ne: ¬∃x, P x): ∀x, ¬(P x) :=
  sorry
example {P: α → Prop}{Q: Prop}(epQ: (∃x, P x) → Q): ∀x, P x → Q :=
  sorry
example {P: α → Prop}{Q: Prop}(apq: ∀x, P x → Q): (∃x, P x) → Q :=
  sorry

-- Сложнее

example {P Q: α → Prop}(aa: (∀x, P x) ∨ (∀x, Q x)): ∀x, P x ∨ Q x :=
  sorry
example {P Q: α → Prop}(ee: (∃x, P x) ∨ (∃x, Q x)): ∃x, P x ∨ Q x :=
  sorry

-- TODO: классическая логика
section classical
open Classical

#check em
#check byContradiction

end classical
 
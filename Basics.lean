-- Коментарий начинается с `--`

-- Указание Lean писать типы рекурсоров полностью
set_option pp.proofs true
-- И не возражать против неиспользуемых переменных
set_option linter.unusedVariables false

example: ∀α β: Type, (x:α) → (y:β) → α :=
  λ(α β: Type)(x:α)(y:β) ↦ x

example (α β: Type)(x:α)(y:β): α := x

def f1 (α β: Type)(x:α)(_:β): α := x

#check f1 Nat Nat 3 5
#reduce f1 Nat Nat 3 5
#print f1

-- Неявные аргументы

#check f1 _ _ 3 5

def f2 {α β: Type}(x:α)(_:β): α := x

#check f2 3 5
#check @f2 Nat Nat 3 5
#check f2 (β := Nat) 3 5

#check λP ↦ ¬P

-- Вселенные

example {α β: Sort u}(x:α)(_:β): α := x
example (x:α)(_:β): α := x

-- Структуры

#print Prod

#check Prod.mk 3 5

#reduce Prod.fst (Prod.mk 3 5)
#reduce Prod.snd (Prod.mk 3 5)

#reduce (Prod.mk 3 5).fst

#check ({fst := 3, snd := 5} : Nat × Nat)
#check (⟨3, 5⟩ : Nat × Nat)

-- Сопоставление с образцом

#reduce
  let (Prod.mk f s) := Prod.mk 3 5
  f

#reduce
  let {fst := f, snd := _} := Prod.mk 3 5
  f

#reduce
  let ⟨f,_⟩ := Prod.mk 3 5
  f

-- То, что мы используем

#check And.intro
#check And.left
#check And.right
#check Or.inl
#check Or.inr
#check Or.elim
#check False.elim

-- Примеры доказательств

example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp ↦ False.elim (np p)) (λq ↦ q)

example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let ⟨p,qr⟩ := pqr
  qr.elim (λq ↦ Or.inl ⟨p,q⟩) (λr ↦ Or.inr ⟨p,r⟩)

example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  ⟨λx ↦ (apq x).left, λx ↦ (apq x).right⟩

example {P: α → β → Prop}(eap: ∃x, ∀y, P x y): ∀y, ∃x, P x y :=
  let ⟨x,ap⟩ := eap
  λy ↦ ⟨x, ap y⟩

-- Упражнения без кванторов

-- Простые упражнения

example {P Q: Prop}(pq: P → Q)(nq: ¬Q): ¬P :=
  sorry
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

-- Упражнения с кванторами

-- Простые

example {P: α → β → Prop}(ap: ∀x, ∀y, P x y): ∀y, ∀x, P x y :=
  sorry
example {P: α → β → Prop}(ep: ∃x, ∃y, P x y): ∃y, ∃x, P x y :=
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

-- Классическая логика

section classical
open Classical

#check em
#check byContradiction

-- Пример
example {P: Prop}(nnp: ¬¬P): P :=
  (em P).elim (λp ↦ p) (λnp ↦ (nnp np).elim)

-- Простые упражнения

example {P Q: Prop}(pq: P → Q): ¬P ∨ Q :=
  sorry

example {P Q: Prop}(npq : ¬(P ∧ Q)): ¬P ∨ ¬Q :=
  sorry

example {P Q: Prop}(np_q: ¬P → Q): ¬Q → P :=
  sorry

example {P Q: Prop}(pq_p: (P → Q) → P): P :=
  sorry

-- Упражнение посложнее
-- (кроме em можно использовать ещё и byContradiction)
example {α: Type}{P: α → Prop}(na: ¬∀x, P x): ∃x, ¬P x :=
  sorry

end classical


-- Равенство

#check Eq.refl
#check Eq.subst
#check Eq.ndrec

-- Eq.symm
example {x y: α}(e: x = y): y = x :=
  e.subst (motive := λt ↦ t = x) (rfl: x = x)

example {x y: α}(e: x = y): y = x :=
  e ▸ (rfl: x = x)

-- Eq.trans
example {x y z: α}(xy: x = y)(yz: y = z): x = z :=
  yz.subst (motive := λt ↦ x = t) (xy: x = y)

-- Eq.congrArg
example {x y: α}{f: α → β}(e: x = y): f x = f y :=
  e.subst (motive := λt ↦ f x = f t) (rfl: f x = f x)

-- Неравенство, на примере Bool

#print Bool
#print Bool.rec
#print Bool.casesOn

#print Bool.noConfusionType

#reduce Bool.noConfusionType False false false  -- False → False
#reduce Bool.noConfusionType False false true   -- False
#reduce Bool.noConfusionType False true false   -- False
#reduce Bool.noConfusionType False true true    -- False → False

def bool_d {P: Sort u}(b: Bool): Bool.noConfusionType P b b :=
  b.casesOn (λp ↦ p) (λp ↦ p)

example (h: false = true): False :=
  Eq.subst (motive := λt ↦ Bool.noConfusionType _ false t) h (bool_d false)

#check Bool.noConfusion

example (h: false = true): False :=
  Bool.noConfusion h

-- Неразличимость доказательств

example (P Q: Prop)(p: P)(q: Q): Or.inl p = Or.inr q :=
  rfl

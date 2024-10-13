set_option pp.proofs true

-- Or.elim
example {c: Prop} (h: Or a b) (left: a → c) (right: b → c): c :=
  Or.rec left right h

-- False.elim
example {C: Sort u} (h: False): C :=
  h.rec

-- Exists.elim
example {α: Sort u} {p: α → Prop} {b: Prop}
    (h₁: Exists (λx => p x)) (h₂: ∀a: α, p a → b): b :=
  Exists.rec h₂ h₁

-- Эквивалентность
#check Iff
#check Iff.intro
#check Iff.mp
#check Iff.mpr

-- Функции равенства
#check rfl
#check Eq.subst
#check Eq.symm
#check Eq.trans
#check congrArg

-- Новые функции
#check id
#check absurd

-- Композиция
#check Function.comp

-- Композицию можно использовать чтобы «применять» функцию к отрицанию
example (nq: ¬q)(h: p → q): ¬p :=
  nq ∘ h

example (np: ¬p): ¬(p ∧ q) :=
  np ∘ And.left

-- `absurd`, но который можно использовать через точку
#check Not.elim

-- Определение натуральных чисел

-- inductive Nat where
-- | zero: Nat
-- | succ (n: Nat): Nat
#check Nat

#print Nat.rec     -- Рекурсор
#print Nat.recOn   -- Также рекурсор
#print Nat.casesOn -- Разбор без рекурсии

-- Сопоставление с образцом
example (n: Nat): Nat :=
  match n with
  | Nat.zero => 1
  | Nat.succ n => n

-- Сложение

-- Определение сложения

-- def Nat.add: Nat → Nat → Nat
-- | a, Nat.zero   => a
-- | a, Nat.succ b => Nat.succ (Nat.add a b)
#check Nat.add

-- Определение с помощью рекурсора
noncomputable
example (n k: Nat): Nat :=
  k.recOn n (λ_ s => Nat.succ s)

-- Различные способы вычислять
#eval 2 + 3
#reduce λn => n + 3

-- Доказательство рефлексивностью
example: 1 + 1 = 2 := rfl

theorem add_zero  (n: Nat):   n + 0 = n                  := rfl
theorem add_one   (n: Nat):   n + 1 = n.succ             := rfl
theorem add_succ  (n k: Nat): n + k.succ = (n + k).succ  := rfl

-- Индуктивное доказательство без тактик
theorem zero_add (n: Nat): 0 + n = n :=
  n.recOn
    (show 0 + 0 = 0 from rfl)
    (λn (h: 0 + n = n) =>
      show 0 + n.succ = n.succ from
      congrArg Nat.succ h)

-- Доказательство сопоставлением с образцом
theorem zero_add_match: (n: Nat) → 0 + n = n
| 0 => show 0 + 0 = 0 from rfl
| Nat.succ n =>
  show 0 + n.succ = n.succ from
  congrArg Nat.succ (zero_add_match n)

-- Доказательство с цепочкой равенств
example (n: Nat): 0 + n = n :=
  n.recOn
    rfl
    (λn (h: 0 + n = n) =>
      calc
        0 + n.succ = (0 + n).succ := add_succ 0 n
        _          = n.succ       := h.symm ▸ (rfl : n.succ = n.succ))

-- Доказательство с тактиками
example (n: Nat): 0 + n = n := by
  refine n.recOn ?z ?s
  · show 0 + 0 = 0
    exact rfl
  · intro n (h: 0 + n = n)
    show 0 + n.succ = n.succ
    exact congrArg Nat.succ h

-- Сжатое доказательство
example (n: Nat): 0 + n = n := by
  refine n.recOn rfl (λn h => ?_)
  rw [add_succ]
  rw [h]

-- Преобразование цели с помощью show
example (n: Nat): 0 + n = n := by
  refine n.recOn rfl (λn h => ?_)
  show (0 + n).succ = n.succ
  rw [h]

-- Тактическое подвыражение
example (n: Nat): 0 + n = n :=
  n.recOn rfl (λn h => by rw [add_succ, h])

-- Упражнения

theorem succ_add (n k: Nat): n.succ + k = (n + k).succ := sorry

theorem add_comm (n k: Nat): n + k = k + n := sorry

-- Ассоциативность сложения

theorem add_assoc (m n k: Nat): (m + n) + k = m + (n + k) := by
  refine k.recOn rfl (λk h => ?_)
  calc
    (m + n) + k.succ = ((m + n) + k).succ := by rw [add_succ]
    _                = (m + (n + k)).succ := by rw [h]
    _                = m + (n + k).succ   := by rw [←add_succ]
    _                = m + (n + k.succ)   := by rw [←add_succ]

-- Сжатое доказательство
example (m n k: Nat): (m + n) + k = m + (n + k) := by
  refine k.recOn rfl (λk h => ?s)
  calc
    (m + n) + k.succ = ((m + n) + k).succ := rfl
    _                = (m + (n + k)).succ := by rw [h]

-- Тактика simp
example {m n k: Nat}: (m + n) + k = m + (n + k) :=
  k.recOn rfl (λk h => by simp only [add_succ, h])


-- Доказательство по ассоциативности и рефлексивности
example (a b c d e: Nat): (((a + b) + c) + d) + e = (c + ((b + e) + a)) + d :=
  by ac_rfl

-- Предшествующее натуральное число
#print Nat.pred

theorem pred_zero: (0: Nat).pred = 0 := rfl
theorem pred_succ (n: Nat): n.succ.pred = n := rfl

-- Упражнения

theorem succ_cancel {n k: Nat}(e: n.succ = k.succ): n = k := sorry

theorem add_right_cancel {m n k: Nat}: (m+k = n+k) → m = n := sorry

theorem add_left_cancel {m n k: Nat}: (k+m = k+n) → m = n := sorry

theorem add_eq_zero_left {n k: Nat}: (n + k = 0) → n = 0 := sorry

theorem add_eq_zero_right {n k: Nat}: (n + k = 0) → k = 0 := sorry

-- Nat.noConfusion
theorem succ_ne_zero (n:Nat): n.succ ≠ 0 := Nat.noConfusion

-- Упражнение
theorem succ_ne_self (n:Nat): n.succ ≠ n := sorry

-- Суммируя, тактики:
-- refine, exact, show, intro, rw, simp, ac_rfl

-- Сравнение

-- «Меньше или равно» это индуктивное семейство типов
#print Nat.le

-- Nat.le.rec: ∀{n: Nat} {motive: ∀k: Nat, n ≤ a → Prop},
--   motive n Nat.le.refl →
--   (∀{k: Nat} (h: n ≤ k), motive k h → motive k.succ (Nat.le.step h)) →
--   ∀{k: Nat} (h: n ≤ k), motive k h
#print Nat.le.rec
#print Nat.le.recOn

-- Eq.rec.{u, v}: ∀{α: Sort v} {a: α} {motive: (b: α) → a = b → Sort u},
--   motive a (Eq.refl a) →
--   ∀{b: α} (t: a = b), motive b t
#print Eq.rec

-- «Меньше» представляет собой `λn k => Nat.le n.succ k`
#print Nat.lt

theorem le_refl (n: Nat): n ≤ n := Nat.le.refl
theorem le_succ (n: Nat): n ≤ n.succ := Nat.le.step (le_refl n)
theorem le_succ_of_le {n k: Nat}: n ≤ k → n ≤ k.succ := Nat.le.step

-- «Меньше или равно» транзитивно
theorem le_trans {m n k: Nat}(mn: m ≤ n)(nk: n ≤ k): m ≤ k :=
  nk.recOn
    (show m ≤ n from mn)
    (λ{k} (_: n ≤ k) (h: m ≤ k) =>
      show m ≤ k.succ from le_succ_of_le h)

-- Транзитивность позволяет использовать calc
example {m n k: Nat}(mn: m ≤ n)(nk: n ≤ k): m ≤ k :=
  calc
    m ≤ n := mn
    n ≤ k := nk

-- Упражнения

theorem le_of_succ_le {n k: Nat}(le: n.succ ≤ k): n ≤ k := sorry

theorem succ_le_succ {n m: Nat}(le: n ≤ m): n.succ ≤ m.succ := sorry

theorem zero_le (n: Nat): 0 ≤ n := sorry

theorem zero_lt_succ (n: Nat): 0 < n.succ := sorry


theorem pred_le (n: Nat): n.pred ≤ n := sorry

theorem pred_lt {n: Nat}(pn: n ≠ 0): n.pred < n := sorry

theorem pred_le_of_le {n k: Nat}(le: n ≤ k): n.pred ≤ k := sorry

theorem pred_le_pred {n k: Nat}(le: n ≤ k): n.pred ≤ k.pred := sorry

theorem le_of_succ_le_succ {n m: Nat}: n.succ ≤ m.succ → n ≤ m := sorry

-- Не самое очевидное доказательство
theorem not_one_le_zero: ¬1 ≤ 0 := by
  suffices any_zero: ∀k, 1 ≤ k → k = 0 → False from
    λh => any_zero 0 h rfl
  exact λk ok => ok.recOn
    (λ(h: 1 = 0) => succ_ne_zero 0 h)
    (λ{k} _ _ (ksz: k.succ = 0) => succ_ne_zero k ksz)

-- Можно без тактик, но тогда нужно явно указывать аргументы
example: ∀k: Nat, 1 ≤ k → k = 0 → False :=
  λk ok => @Nat.le.recOn _ (λk _ => k = 0 → False) k ok
    (λ(h: 1 = 0) => succ_ne_zero 0 h)
    (λ{k} _ _ (ksz: k.succ = 0) => succ_ne_zero k ksz)

-- Упражнения

theorem not_succ_le_zero (n: Nat): ¬n.succ ≤ 0 := sorry

theorem not_succ_le_self (n: Nat): ¬n.succ ≤ n := sorry

theorem eq_zero_of_le_zero {n: Nat} (h: n ≤ 0): n = 0 := sorry

theorem lt_irrefl (n: Nat): ¬n < n := sorry

theorem pos_iff_ne_zero {n: Nat}: 0 < n ↔ n ≠ 0 :=
  ⟨sorry, sorry⟩

-- Упражнения, связывающие «меньше или равно» со сложением

theorem le_add (n k: Nat): n ≤ n + k := sorry

theorem le_add_of_le {m n: Nat}(k: Nat)(le: m ≤ n): m ≤ n + k := sorry

theorem add_le_add_left {n k: Nat}(l: n ≤ k): ∀p, n + p ≤ k + p := sorry

theorem le_of_add_le_add_left {m n k: Nat}: (h: m + n ≤ m + k) → n ≤ k := sorry

theorem not_add_le_self (n: Nat){k: Nat}(pk: 0 < k): ¬(n + k ≤ n) := sorry

-- Пара полезных лемм

#check Nat.exists_eq_add_of_le
theorem exists_of_le {n k: Nat}(le: n ≤ k): ∃p, n + p = k :=
  le.recOn
    ⟨0, rfl⟩
    (λ_ ⟨p,h⟩ => ⟨p.succ, congrArg Nat.succ h⟩)

theorem le_of_exists {n k: Nat}: (ex: ∃d, n + d = k) → n ≤ k := by
  refine k.recOn ?_ ?_
  · intro ex
    show n ≤ 0
    let ⟨d, (hd: n + d = 0)⟩ := ex
    suffices nz: n = 0 from nz ▸ le_refl n
    exact add_eq_zero_left hd
  · intro k _ ex
    show n ≤ k.succ
    let ⟨d, (hd: n + d = k.succ)⟩ := ex
    suffices h: n ≤ n + d from hd ▸ h
    exact le_add n d

-- Ещё упражнения

theorem le_antisymm {n k: Nat}(nk: n ≤ k): (kn: k ≤ n) → n = k := sorry

theorem eq_or_lt_of_le {n m: Nat}(nm: n ≤ m): (n = m) ∨ (n < m) := by
  suffices h: ∀m, n ≤ m → (n = m) ∨ (n < m) from h m nm
  sorry

theorem lt_or_ge (n k: Nat): n < k ∨ k ≤ n :=
  suffices h: ∀n, n < k ∨ k ≤ n from h n
  sorry

theorem not_le_of_gt {n k: Nat}(h: n > k): ¬n ≤ k := sorry

theorem not_lt_of_ge {n k: Nat}(h: k ≥ n): ¬(k < n) := sorry

-- `≤` это на самом деле `LE.le`
#check LE.le

-- Инстанс класса для типа натуральных чисел
#synth LE Nat    -- instLENat
#print instLENat

-- Ещё классы и их инстансы

#check HAdd
#synth HAdd Nat Nat Nat    -- instHAdd
#check instHAdd

#synth Add Nat    -- instAddNat
#check instAddNat

-- Разрешимость это класс
#check Decidable

-- `≤` разрешимо
#synth ∀n k: Nat, Decidable (n ≤ k)    -- Nat.decLe

def decLe: (n m: Nat) → Decidable (n ≤ m)
| Nat.zero, Nat.zero     => Decidable.isTrue (le_refl 0)
| Nat.zero, m            => Decidable.isTrue (zero_le m)
| Nat.succ n, Nat.zero   => Decidable.isFalse (not_succ_le_zero n)
| Nat.succ n, Nat.succ m =>
  match decLe n m with
  | Decidable.isTrue h  => Decidable.isTrue (succ_le_succ h)
  | Decidable.isFalse h => Decidable.isFalse (h ∘ le_of_succ_le_succ)

-- `true` если высказывание истинно, `false` если ложно
#check decide

-- Равенства для `decide`

#check decide_eq_false
example [inst : Decidable p]: ¬p → (decide p) = false :=
  inst.recOn (λ_ _ => rfl) (λhp hnp => absurd hp hnp)

#check decide_eq_true
example [inst : Decidable p]: p → (decide p) = true :=
  inst.recOn (λhnp hp => absurd hp hnp) (λ_ _ => rfl)

-- Доказательство p из (decide p) = true
#check of_decide_eq_true
example [inst: Decidable p](eq: (decide p) = true): p :=
  match (generalizing := false) inst with
  | isTrue h => h
  | isFalse h => absurd eq (ne_true_of_eq_false (decide_eq_false h))

-- Доказательство разрешимостью
example: 0 ≤ 2 := of_decide_eq_true rfl
example: 0 ≤ 2 := by decide

-- Выражение if ... then ... else
#check ite

-- Пример использования
example (n k: Nat): Bool :=
  if n ≤ k then
    true
  else
    false

-- Выражение if h: ... then ... else
#check dite

-- Пример
example [Decidable p]: p ∨ ¬p :=
  if h: p then Or.inl h
  else Or.inr h

-- Леммы для if ... then ... else
#check if_pos
#check if_neg

-- Леммы для if h: ... then ... else
#check dif_pos
#check dif_neg


-- Вычитание

-- Определение вычитания

-- def Nat.sub: Nat → Nat → Nat
-- | a, 0          => a
-- | a, Nat.succ b => pred (Nat.sub a b)
#check Nat.sub

#reduce 3 - 2    -- 1
#reduce 2 - 3    -- 0

theorem sub_zero (n: Nat): n - 0 = n := rfl
theorem sub_succ (n k: Nat): n - k.succ = (n - k).pred := rfl

-- Упражнения

theorem zero_sub (n: Nat): 0 - n = 0 := sorry

theorem succ_sub_succ (n m: Nat): n.succ - m.succ = n - m := sorry

theorem sub_self (n: Nat): n - n = 0 := sorry

theorem sub_eq_zero_of_le {n k: Nat}(h: n ≤ k): n - k = 0 := sorry

theorem sub_le (n m: Nat): n - m ≤ n := sorry

-- Пример одновременного сопоставления двух значений
theorem sub_lt {n m: Nat}(pn: 0 < n)(pm: 0 < m): n - m < n :=
  match n, m with
  | Nat.zero, _ => absurd pn (lt_irrefl 0)
  | _, Nat.zero => absurd pm (lt_irrefl 0)
  | Nat.succ n, Nat.succ m =>
    calc
      n.succ - m.succ = n - m  := by rw [succ_sub_succ]
      _               < n.succ := succ_le_succ (sub_le n m)

-- Ещё упражнения

theorem sub_le_sub_left {n m: Nat}(h: n ≤ m)(k: Nat): k - m ≤ k - n := sorry

theorem sub_le_sub_right {n m: Nat} (le: n ≤ m) (k: Nat): n - k ≤ m - k :=
  suffices h: ∀k, n ≤ m → n - k ≤ m - k from h k le
  sorry

theorem sub_sub (n m k: Nat): n - m - k = n - (m + k) := sorry

theorem add_sub_cancel (n m: Nat): n + m - m = n := sorry

theorem succ_sub {n k: Nat}(h: k ≤ n): n.succ - k = (n - k).succ := by
  let ⟨d, hd⟩ := exists_of_le h
  rw [←hd]
  sorry

theorem sub_add_comm {n m k: Nat}(h: k ≤ n): n + m - k = n - k + m := sorry

theorem sub_add_cancel {n k: Nat} (h: k ≤ n): n - k + k = n := sorry

theorem add_sub_assoc {m k: Nat} (h: k ≤ m) (n: Nat): n + m - k = n + (m - k) := by
  let ⟨d, hd⟩ := exists_of_le h
  rw [←hd]
  sorry


-- Умножение

-- Определение умножения

-- def Nat.mul: Nat → Nat → Nat
-- | a, Nat.zero   => a
-- | a, Nat.succ b => Nat.add (Nat.mul a b) a
#check Nat.mul

theorem mul_zero (n: Nat):   n * 0 = 0               := rfl
theorem mul_succ (n k: Nat): n * k.succ = n * k + n  := rfl

-- Упражнения

theorem mul_one (n: Nat):    n * 1 = n := sorry

theorem zero_mul (n: Nat): 0 * n = 0 := sorry

theorem succ_mul (n k: Nat): n.succ * k = n * k + k := sorry

theorem one_mul (n:Nat): 1*n = n := sorry

-- Упражнения (коммутативность, дистрибутивность и ассоциативность)

theorem mul_comm (n k: Nat): n * k = k * n := sorry

theorem mul_left_distr (n k p: Nat): n * (k + p) = n * k + n * p := sorry

theorem mul_right_distr (n k p: Nat): (n + k) * p = n * p + k * p := sorry

theorem mul_assoc (m n k: Nat): (m * n) * k = m * (n * k) := sorry

example {a b c d e: Nat}: (((a * b) * c) * d) * e = (c * ((b * e) * a)) * d :=
by ac_rfl

-- Ещё упражнения
theorem mul_eq_zero {n k: Nat}: (n * k = 0) → n = 0 ∨ k = 0 := sorry

theorem mul_left_cancel {m n k: Nat}(pm: m ≠ 0): (m * n = m * k) → n = k := by
  suffices h: ∀n, (m * n = m * k) → n = k from h n
  refine k.recOn ?_ ?_
  · sorry
  · sorry

theorem pos_of_mul_pos_left {n k: Nat}(h: 0 < n * k): 0 < k := sorry

theorem mul_le_mul_left {n k: Nat}(m: Nat)(h: n ≤ k): m * n ≤ m * k := sorry

theorem le_of_mul_le_mul_left {m n k: Nat}(pk: 0 < m): (m * n ≤ m * k) → n ≤ k :=
  match lt_or_ge k n with
  | Or.inr h => sorry
  | Or.inl (nm: k < n) => sorry

theorem mul_sub_left_distrib (m n k: Nat): m * (n - k) = m * n - m * k :=
  if h: n ≥ k then sorry
  else sorry


-- Сильная индукция

#check Nat.strongInductionOn
#print Nat.strongInductionOn

#print Nat.div
#check measure

-- Отношение последователя
def Nat.succRel (n k: Nat) := n.succ = k

-- Индуктивные отношения
def Ind.{u} (r: α → α → Prop) :=
  ∀{M: α → Sort u}, (∀x, (∀y, r y x → M y) → M x) → ∀x, M x

-- Nat.succRel индуктивно
def indSuccRel: Ind Nat.succRel :=
  λ{M} (ind: ∀x, (∀y: Nat, y.succRel x → M y) → M x) => by
    refine Nat.rec ?z (λn (h: M n) => ?_)
    · show M 0
      exact ind 0 (λn s => absurd s (succ_ne_zero n))
    · suffices hk: ∀k, k.succRel n.succ → M k from ind n.succ hk
      intro k s
      have: k = n := congrArg Nat.pred s
      exact this ▸ h

-- Достижимость

-- inductive Acc {α: Sort u}(r: α → α → Prop): α → Prop where
-- | intro (x: α)(h: (y: α) → r y x → Acc r y): Acc r x
#print Acc

#print Acc.rec
#check Acc.recOn

-- Любое индуктивное отношение является фундированным
def wf_of_ind {r: α → α → Prop}(ind: Ind r): ∀x, Acc r x :=
  ind Acc.intro

-- Любое фундированное отношение является индуктивным
noncomputable def ind_of_wf {r: α → α → Prop}(wf: ∀x, Acc r x): Ind r :=
  λ{M} (h: ∀x, (∀y, r y x → M y) → M x) x =>
    show M x from (wf x).recOn (λx _ (wh: ∀y, r y x → M y) => h x wh)

-- Любое число достижимо по Nat.succRel
theorem acc_succ_rel: ∀n, Acc Nat.succRel n :=
  wf_of_ind indSuccRel

-- Достижимость числа 3 как выражение
#reduce acc_succ_rel 3

#check Acc.inv
example {x y: α}(ax: Acc r x): r y x → Acc r y :=
  ax.recOn (λx (f: ∀y, r y x → Acc r y) _ => f y)

-- Отношение «меньше или равно» является фундированным
def lt_wf (n: Nat): Acc Nat.lt n := by
  refine n.recOn (Acc.intro 0 ?_) ?_
  · intro y (h: y < 0)
    exact absurd h (not_succ_le_zero y)
  · intro n (an: Acc Nat.lt n)
    suffices ih: ∀m, m < n.succ → Acc Nat.lt m from Acc.intro n.succ ih
    intro m h
    have elt: m = n ∨ m < n := eq_or_lt_of_le (le_of_succ_le_succ h)
    exact elt.elim
      (λ(e: m = n) => e.symm ▸ an)
      (λ(l: m < n) => Acc.inv an l)

-- Определение функции с помощью сильной индукции

def modTwoStep (n: Nat) (f: ∀k: Nat, k < n → Nat): Nat :=
  if h: n ≥ 2 then
    have: n - 2 + 1 ≤ n := sub_add_comm h ▸ sub_le n 1
    f (n - 2) this
  else n

noncomputable
def modTwoFix: Nat → Nat :=
  ind_of_wf lt_wf modTwoStep

#reduce modTwoFix 3

-- Прообраз отношения для функции

-- def InvImage {α: Sort u} {β: Sort v} (r: β → β → Prop) (f: α → β): α → α → Prop :=
--   fun a₁ a₂ => r (f a₁) (f a₂)
#check InvImage

-- Достижим образ — достижим и прообраз
def acc_invImage {x: α}(f: α → β)(acc: Acc r (f x)): Acc (InvImage r f) x := by
  suffices h: ∀y, Acc r y → ∀w, f w = y → Acc (InvImage r f) w
    from h (f x) acc x rfl
  refine λy (a: Acc r y) => a.recOn ?_
  intro z _ (h: ∀y, r y z → ∀t, f t = y → Acc (InvImage r f) t)
  show ∀w, f w = z → Acc (InvImage r f) w
  intro w e
  suffices h: ∀t, r (f t) (f w) → Acc (InvImage r f) t
    from Acc.intro _ h
  exact λt ht => h _ (e ▸ ht) t rfl

-- Прообраз фундированного отношения это фундированное отношение
def wf_invImage (wf: ∀y: β, Acc r y)(f: α → β): ∀x: α, Acc (InvImage r f) x :=
  λx => acc_invImage f (wf (f x))

-- Мера задаёт фундированное отношение
def wf_measure: (f: α → Nat) → ∀x: α, Acc (InvImage Nat.lt f) x :=
  wf_invImage lt_wf

-- Использование меры
noncomputable example (m: α → Nat)(step: ∀x: α, (∀y: α, m y < m x → α) → α): α → α :=
  ind_of_wf (wf_measure m) step

-- Определениие функции с `termination_by` и `decreasing_by`
def modTwo (n: Nat): Nat :=
  if h: n ≥ 2 then modTwo (n - 2)
  else n
termination_by n
decreasing_by
  simp_wf
  show n - 2 + 1 ≤ n
  exact sub_add_comm h ▸ sub_le n 1

-- Принцип бесконечного спуска
def inf_desc {r: α → α → Prop}(arx: Acc r x){p: α → Prop}
    (h: ∀x, p x → ∃y, r y x ∧ p y): p x → False :=
  arx.recOn (λx _ (ih: ∀y, r y x → p y → False) px =>
    let ⟨y, ⟨ryx, py⟩⟩ := h x px
    ih y ryx py)


-- Деление

def div_rec_lemma {n k: Nat}: (0 < k ∧ k ≤ n) → n - k < n :=
  λ⟨(pk: 0 < k), (kn: k ≤ n)⟩ => sub_lt (le_trans pk kn) pk

-- Определение деления

-- def Nat.div (n k: Nat) : Nat :=
--  if h: 0 < k ∧ k ≤ n then
--    Nat.div (n - k) k + 1
--  else
--    0
-- termination_by n
-- decreasing_by exact div_rec_lemma h
#check Nat.div

-- Определение модуля (остатка от деления)

-- def modCore (n k: Nat): Nat :=
--   if h: 0 < k ∧ k ≤ n then
--     modCore (n - k) k
--   else
--     n
-- termination_by n
-- decreasing_by exact div_rec_lemma h
--
-- def Nat.mod: Nat → Nat → Nat
-- | 0, _ => 0
-- | x, y => modCore x y
#check Nat.mod

-- Леммы из стандартной библиотеки

theorem div_eq (n k: Nat): n / k = if 0 < k ∧ k ≤ n then (n - k) / k + 1 else 0 :=
  Nat.div_eq n k

theorem mod_eq (n k: Nat): n % k = if 0 < k ∧ k ≤ n then (n - k) % k else n :=
  Nat.mod_eq n k

-- Комбинации этих лемм с if_pos/if_neg

theorem div_eq_if_pos {n k: Nat}(h: 0 < k ∧ k ≤ n): n / k = (n - k) / k + 1 :=
  by rw [div_eq, if_pos h]

theorem div_eq_if_neg {n k: Nat}(h: ¬(0 < k ∧ k ≤ n)): n / k = 0 :=
  by rw [div_eq, if_neg h]

theorem mod_eq_if_pos {n k: Nat}(h: 0 < k ∧ k ≤ n): n % k = (n - k) % k :=
  by rw [mod_eq, if_pos h]

theorem mod_eq_if_neg {n k: Nat}(h: ¬(0 < k ∧ k ≤ n)): n % k = n :=
  by rw [mod_eq, if_neg h]

-- Пример использования
theorem mod_zero (n: Nat): n % 0 = n := by
  have: ¬(0 < 0 ∧ 0 ≤ n) := lt_irrefl 0 ∘ And.left
  rw [mod_eq_if_neg this]

-- Упражнения

theorem mod_eq_of_lt {n k: Nat}(h: n < k): n % k = n := sorry

theorem mod_eq_sub_mod {n k: Nat}(h: n ≥ k): n % k = (n - k) % k := sorry

theorem mod_one (n: Nat): n % 1 = 0 := sorry

theorem zero_mod (n: Nat): 0 % n = 0 := sorry

theorem zero_div (n: Nat): 0 / n = 0 := sorry

theorem div_one (n: Nat): n / 1 = n := sorry

-- Индуктивный принцип, извлечённый из определений деления и модуля
def divmod_ind.{u}
    {motive: Nat → Nat → Sort u}
    (base: ∀n k, ¬(0 < k ∧ k ≤ n) → motive n k)
    (ind: ∀n k, 0 < k ∧ k ≤ n → motive (n - k) k → motive n k)
    (n k: Nat): motive n k :=
  if h: 0 < k ∧ k ≤ n then
    ind n k h (divmod_ind base ind (n - k) k)
  else
    base n k h
termination_by n
decreasing_by exact div_rec_lemma h

-- Использование этого принципа
theorem mod_add_div (n k: Nat): n % k + k * (n / k) = n := by
  refine divmod_ind (motive := λn k => n % k + k * (n / k) = n) ?_ ?_ n k
  · intro n k (h: ¬(0 < k ∧ k ≤ n))
    calc
      n % k + k * (n / k) = n + k * 0 := by rw [div_eq_if_neg h, mod_eq_if_neg h]
      _                   = n         := by rw [mul_zero, add_zero]
  · intro n k (h: 0 < k ∧ k ≤ n)
    intro (ih: (n - k) % k + k * ((n - k) / k) = n - k)
    calc
      n % k + k * (n / k) = (n - k) % k + k * ((n - k) / k + 1) :=
        by rw [div_eq_if_pos h, mod_eq_if_pos h]
      _ = (n - k) % k + k * ((n - k) / k) + k :=
        by simp only [add_assoc, mul_succ]
      _ = n :=
        by simp only [ih, sub_add_cancel h.right]

-- Упражнения (связь со сложением и умножением)

theorem add_div_right (n: Nat){k: Nat}(h: 0 < k): (n + k) / k = (n / k).succ := sorry

theorem add_mod_right (n k: Nat): (n + k) % k = n % k := sorry

theorem add_mod_left (n k: Nat): (k + n) % k = n % k := sorry

theorem add_mul_div_left (m n: Nat){k: Nat}(h: 0 < k): (m + k * n) / k = m / k + n := sorry

theorem mul_div_cancel (m: Nat){n: Nat}(h: 0 < n): m * n / n = m := sorry

theorem add_mul_mod_self_left (m n k: Nat): (m + k * n) % k = m % k := sorry

theorem add_mul_mod_self_right (m n k: Nat): (m + n * k) % k = m % k := sorry

theorem mul_mod_left (n k: Nat): n * k % k = 0 := sorry

theorem mul_mod_right (n k: Nat): k * n % k = 0 := sorry

-- Упражнения (свойста модуля)

theorem mod_lt (n: Nat){k: Nat}: 0 < k → n % k < k := sorry

theorem mod_mod (n k: Nat): n % k % k = n % k := sorry

-- Неочевидная теорема
theorem mul_mod_mul_left (m n k: Nat): m * n % (m * k) = m * (n % k) := by
  match m with
  | Nat.zero => simp only [zero_mul, mod_zero]
  | Nat.succ m =>
    refine divmod_ind
      (motive := λn k => m.succ * n % (m.succ * k) = m.succ * (n % k)) ?_ ?_ n k
    · intro n k (h: ¬(0 < k ∧ k ≤ n))
      have: ¬(0 < m.succ * k ∧ m.succ * k ≤ m.succ * n) :=
        h ∘ (λ⟨msk, k_le_msn⟩ =>
          ⟨pos_of_mul_pos_left msk,
          le_of_mul_le_mul_left (zero_lt_succ m) k_le_msn⟩)
      calc
        m.succ * n % (m.succ * k) = m.succ * n       := by rw [mod_eq_if_neg this]
        m.succ * n                = m.succ * (n % k) := by rw [mod_eq_if_neg h]
    · intro n k ⟨_, (yx: k ≤ n)⟩
      intro (h2: m.succ * (n - k) % (m.succ * k) = m.succ * ((n - k) % k))
      calc
        m.succ * n % (m.succ * k) = (m.succ * n - m.succ * k) % (m.succ * k) :=
          by rw [mod_eq_sub_mod (mul_le_mul_left _ yx)]
        _ = (m.succ * (n - k)) % (m.succ * k) :=
          by simp only [mul_sub_left_distrib]
        _ = m.succ * ((n - k) % k) := h2
        _ = m.succ * (n % k)       := by rw [←mod_eq_sub_mod yx]

-- Упражнения

theorem add_mod (m n k: Nat): (m + n) % k = (m % k + n % k) % k := sorry

theorem mul_mod (m n k: Nat): (m * n) % k = ((m % k) * (n % k)) % k := sorry


-- Тактика `omega`
example: 2*a + b = a + b + a := by omega

-- Тактики, помогающие найти леммы
#check Lean.Parser.Tactic.exact?
#check Lean.Parser.Tactic.apply?

-- Леммы можно ещё искать на https://loogle.lean-lang.org/

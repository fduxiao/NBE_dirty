
import Std.Data.TreeMap


abbrev FinMap V := List V


def FinMap.lookup {V}: Nat -> FinMap V -> Option V
  | i, l =>
    let l': List V := l
    l'[i]?



@[simp]
theorem FinMap.lookup_nil {V} {n: Nat}:
  FinMap.lookup (V := V) n [] = none
:= by
  simp [lookup]


@[simp]
theorem FinMap.lookup_zero {V} {M: FinMap V} {x: V}:
  FinMap.lookup 0 (x :: M) = x
:= by
  simp [lookup]


@[simp]
theorem FinMap.lookup_succ {V} {M: FinMap V} {v: V} {i: Nat}:
  FinMap.lookup (i + 1) (v :: M) = FinMap.lookup i M
:= by
  induction M with
  | nil =>
    simp [lookup]
  | cons =>
    simp [lookup]


@[simp]
theorem FinMap.lookup_concat_length {V} {M: FinMap V} {v: V}:
  FinMap.lookup M.length (M ++ [v]) = some v
:= by
  apply List.getElem?_concat_length



@[simp]
theorem FinMap.lookup_len_app {V} {M M': FinMap V} {i: Nat}:
  FinMap.lookup (i + M'.length) (M' ++ M) = FinMap.lookup i M
:= by
  induction M' with
  | nil =>
    simp [lookup]
  | cons x xs IH =>
    simp
    conv =>
      lhs
      lhs
      rewrite [<-Nat.add_assoc]
    simp
    exact IH


theorem FinMap.lookup_some_lt {V} {M: FinMap V} {i: Nat} {v}:
  M.lookup i = some v -> i < M.length
:= by
  intro H
  have H := List.getElem?_eq_some_iff.mp H
  exact H.choose


theorem FinMap.lookup_lt_some {V} {M: FinMap V} {i: Nat}:
  (h: i < M.length) -> M.lookup i = M[i]'h
:= by
  intro H
  apply List.getElem?_eq_getElem H


theorem FinMap.lookup_ge {V} {M: FinMap V} {i: Nat}:
  i ≥ M.length -> M.lookup i = none
:= by
  intro H
  apply List.getElem?_eq_none
  simp_all


theorem FinMap.lookup_left {V} {M M': FinMap V} {i: Nat}:
  (i < M.length) ->
  FinMap.lookup i (M ++ M') = FinMap.lookup i M
:= by
  intro H
  apply List.getElem?_append_left
  exact H


theorem FinMap.lookup_right {V} {M M': FinMap V} {i: Nat}:
  (i ≥ M.length) ->
  FinMap.lookup i (M ++ M') = FinMap.lookup (i - M.length) M'
:= by
  intro H
  apply List.getElem?_append_right
  exact H


def FinMap.update {V} (v: V): FinMap V -> FinMap V := List.cons v


@[simp]
theorem FinMap.lookup_cons_concat_length {V} {M M': FinMap V} {v: V}:
  FinMap.lookup M.length (M ++ v :: M') = some v
:= by
  have H: M.length ≥ M.length := by omega
  simp [FinMap.lookup_right H]


def FinMap.lookupD {V} (n: Nat) (d: V) (M: FinMap V): V :=
  match M.lookup n with
  | .some v => v
  | .none => d


@[simp]
theorem FinMap.lookupD_nil {V} {n: Nat} {d: V}:
  FinMap.lookupD n d [] = d
:= by
  simp [lookupD]

@[simp]
theorem FinMap.lookupD_zero {V} {M: FinMap V} {x: V} {d}:
  FinMap.lookupD 0 d (x :: M) = x
:= by
  simp [lookupD]


@[simp]
theorem FinMap.lookupD_succ {V} {M: FinMap V} {x: V} {d} {i}:
  FinMap.lookupD (i + 1) d (x :: M) = FinMap.lookupD i d M
:= by
  simp [lookupD]



theorem FinMap.lookupD_lt {V} {M: FinMap V} {i: Nat} {d}:
  (h: i < M.length) -> M.lookupD i d = M[i]
:= by
  intro H
  unfold lookupD
  simp [FinMap.lookup_lt_some H]


theorem FinMap.lookupD_ge {V} {M: FinMap V} {i: Nat} {d}:
  (h: i ≥ M.length) -> M.lookupD i d = d
:= by
  intro H
  unfold lookupD
  simp [FinMap.lookup_ge H]

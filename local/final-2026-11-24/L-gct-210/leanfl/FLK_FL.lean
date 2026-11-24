import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_210_aux.FLK

open Finset

noncomputable section

abbrev M55 (Kf : Type) := Fin 5 × Fin 5 → Kf

abbrev M45 (Kf : Type) := Fin 4 × Fin 5 → Kf

set_option maxHeartbeats 800000 in
abbrev V4 (Kf : Type) := Fin 4 → Kf

variable {Kf : Type} [Field Kf] [NeZero (2 : Kf)] [NeZero (3 : Kf)] [NeZero (5 : Kf)]

@[simp] theorem nz2 : (2 : Kf) ≠ 0 := NeZero.ne (2 : Kf)

@[simp] theorem nz3 : (3 : Kf) ≠ 0 := NeZero.ne (3 : Kf)

@[simp] theorem nz5 : (5 : Kf) ≠ 0 := NeZero.ne (5 : Kf)

@[simp] theorem nz4 : (4 : Kf) ≠ 0 := by
  have e : (4 : Kf) = 2 * 2 := by norm_num
  rw [e]
  exact mul_ne_zero nz2 nz2

@[simp] theorem nz6 : (6 : Kf) ≠ 0 := by
  have e : (6 : Kf) = 2 * 3 := by norm_num
  rw [e]
  exact mul_ne_zero nz2 nz3

@[simp] theorem nz8 : (8 : Kf) ≠ 0 := by
  have e : (8 : Kf) = 2 * 4 := by norm_num
  rw [e]
  exact mul_ne_zero nz2 nz4

@[simp] theorem nz9 : (9 : Kf) ≠ 0 := by
  have e : (9 : Kf) = 3 * 3 := by norm_num
  rw [e]
  exact mul_ne_zero nz3 nz3

@[simp] theorem nz10 : (10 : Kf) ≠ 0 := by
  have e : (10 : Kf) = 2 * 5 := by norm_num
  rw [e]
  exact mul_ne_zero nz2 nz5

@[simp] theorem nz12 : (12 : Kf) ≠ 0 := by
  have e : (12 : Kf) = 3 * 4 := by norm_num
  rw [e]
  exact mul_ne_zero nz3 nz4

@[simp] theorem nz15 : (15 : Kf) ≠ 0 := by
  have e : (15 : Kf) = 3 * 5 := by norm_num
  rw [e]
  exact mul_ne_zero nz3 nz5

@[simp] theorem nz16 : (16 : Kf) ≠ 0 := by
  have e : (16 : Kf) = 4 * 4 := by norm_num
  rw [e]
  exact mul_ne_zero nz4 nz4

@[simp] theorem nz18 : (18 : Kf) ≠ 0 := by
  have e : (18 : Kf) = 2 * 9 := by norm_num
  rw [e]
  exact mul_ne_zero nz2 nz9

@[simp] theorem nz20 : (20 : Kf) ≠ 0 := by
  have e : (20 : Kf) = 4 * 5 := by norm_num
  rw [e]
  exact mul_ne_zero nz4 nz5

@[simp] theorem nz24 : (24 : Kf) ≠ 0 := by
  have e : (24 : Kf) = 4 * 6 := by norm_num
  rw [e]
  exact mul_ne_zero nz4 nz6

@[simp] theorem nz30 : (30 : Kf) ≠ 0 := by
  have e : (30 : Kf) = 5 * 6 := by norm_num
  rw [e]
  exact mul_ne_zero nz5 nz6

@[simp] theorem nz32 : (32 : Kf) ≠ 0 := by
  have e : (32 : Kf) = 4 * 8 := by norm_num
  rw [e]
  exact mul_ne_zero nz4 nz8

@[simp] theorem nz36 : (36 : Kf) ≠ 0 := by
  have e : (36 : Kf) = 6 * 6 := by norm_num
  rw [e]
  exact mul_ne_zero nz6 nz6

@[simp] theorem nz40 : (40 : Kf) ≠ 0 := by
  have e : (40 : Kf) = 5 * 8 := by norm_num
  rw [e]
  exact mul_ne_zero nz5 nz8

@[simp] theorem nz45 : (45 : Kf) ≠ 0 := by
  have e : (45 : Kf) = 5 * 9 := by norm_num
  rw [e]
  exact mul_ne_zero nz5 nz9

@[simp] theorem nz48 : (48 : Kf) ≠ 0 := by
  have e : (48 : Kf) = 6 * 8 := by norm_num
  rw [e]
  exact mul_ne_zero nz6 nz8

@[simp] theorem nz60 : (60 : Kf) ≠ 0 := by
  have e : (60 : Kf) = 6 * 10 := by norm_num
  rw [e]
  exact mul_ne_zero nz6 nz10

@[simp] theorem nz64 : (64 : Kf) ≠ 0 := by
  have e : (64 : Kf) = 8 * 8 := by norm_num
  rw [e]
  exact mul_ne_zero nz8 nz8

@[simp] theorem nz72 : (72 : Kf) ≠ 0 := by
  have e : (72 : Kf) = 8 * 9 := by norm_num
  rw [e]
  exact mul_ne_zero nz8 nz9

@[simp] theorem nz96 : (96 : Kf) ≠ 0 := by
  have e : (96 : Kf) = 8 * 12 := by norm_num
  rw [e]
  exact mul_ne_zero nz8 nz12

@[simp] theorem nz120 : (120 : Kf) ≠ 0 := by
  have e : (120 : Kf) = 10 * 12 := by norm_num
  rw [e]
  exact mul_ne_zero nz10 nz12

@[simp] theorem nz144 : (144 : Kf) ≠ 0 := by
  have e : (144 : Kf) = 12 * 12 := by norm_num
  rw [e]
  exact mul_ne_zero nz12 nz12

@[simp] theorem nz288 : (288 : Kf) ≠ 0 := by
  have e : (288 : Kf) = 2 * 144 := by norm_num
  rw [e]
  exact mul_ne_zero nz2 nz144

@[simp] theorem nz128 : (128 : Kf) ≠ 0 := by
  have e : (128 : Kf) = 2 * 64 := by norm_num
  rw [e]
  exact mul_ne_zero nz2 nz64

@[simp] theorem nz256 : (256 : Kf) ≠ 0 := by
  have e : (256 : Kf) = 4 * 64 := by norm_num
  rw [e]
  exact mul_ne_zero nz4 nz64

@[simp] theorem zn2 : (0 : Kf) ≠ 2 := fun h => nz2 h.symm

@[simp] theorem zn3 : (0 : Kf) ≠ 3 := fun h => nz3 h.symm

@[simp] theorem zn5 : (0 : Kf) ≠ 5 := fun h => nz5 h.symm

@[simp] theorem zn4 : (0 : Kf) ≠ 4 := fun h => nz4 h.symm

@[simp] theorem zn6 : (0 : Kf) ≠ 6 := fun h => nz6 h.symm

@[simp] theorem zn8 : (0 : Kf) ≠ 8 := fun h => nz8 h.symm

@[simp] theorem zn9 : (0 : Kf) ≠ 9 := fun h => nz9 h.symm

@[simp] theorem zn10 : (0 : Kf) ≠ 10 := fun h => nz10 h.symm

@[simp] theorem zn12 : (0 : Kf) ≠ 12 := fun h => nz12 h.symm

@[simp] theorem zn15 : (0 : Kf) ≠ 15 := fun h => nz15 h.symm

@[simp] theorem zn16 : (0 : Kf) ≠ 16 := fun h => nz16 h.symm

@[simp] theorem zn18 : (0 : Kf) ≠ 18 := fun h => nz18 h.symm

@[simp] theorem zn20 : (0 : Kf) ≠ 20 := fun h => nz20 h.symm

@[simp] theorem zn24 : (0 : Kf) ≠ 24 := fun h => nz24 h.symm

@[simp] theorem zn30 : (0 : Kf) ≠ 30 := fun h => nz30 h.symm

@[simp] theorem zn32 : (0 : Kf) ≠ 32 := fun h => nz32 h.symm

@[simp] theorem zn36 : (0 : Kf) ≠ 36 := fun h => nz36 h.symm

@[simp] theorem zn40 : (0 : Kf) ≠ 40 := fun h => nz40 h.symm

@[simp] theorem zn45 : (0 : Kf) ≠ 45 := fun h => nz45 h.symm

@[simp] theorem zn48 : (0 : Kf) ≠ 48 := fun h => nz48 h.symm

@[simp] theorem zn60 : (0 : Kf) ≠ 60 := fun h => nz60 h.symm

@[simp] theorem zn64 : (0 : Kf) ≠ 64 := fun h => nz64 h.symm

@[simp] theorem zn72 : (0 : Kf) ≠ 72 := fun h => nz72 h.symm

@[simp] theorem zn96 : (0 : Kf) ≠ 96 := fun h => nz96 h.symm

@[simp] theorem zn120 : (0 : Kf) ≠ 120 := fun h => nz120 h.symm

@[simp] theorem zn144 : (0 : Kf) ≠ 144 := fun h => nz144 h.symm

@[simp] theorem zn288 : (0 : Kf) ≠ 288 := fun h => nz288 h.symm

@[simp] theorem zn128 : (0 : Kf) ≠ 128 := fun h => nz128 h.symm

@[simp] theorem zn256 : (0 : Kf) ≠ 256 := fun h => nz256 h.symm

@[simp] theorem ne1_2 : (1 : Kf) ≠ 2 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne2_1 : (2 : Kf) ≠ 1 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne1_3 : (1 : Kf) ≠ 3 := by
  intro h
  exact nz2 (show (2 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne3_1 : (3 : Kf) ≠ 1 := by
  intro h
  exact nz2 (show (2 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne1_4 : (1 : Kf) ≠ 4 := by
  intro h
  exact nz3 (show (3 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne4_1 : (4 : Kf) ≠ 1 := by
  intro h
  exact nz3 (show (3 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne1_5 : (1 : Kf) ≠ 5 := by
  intro h
  exact nz4 (show (4 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne5_1 : (5 : Kf) ≠ 1 := by
  intro h
  exact nz4 (show (4 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne1_6 : (1 : Kf) ≠ 6 := by
  intro h
  exact nz5 (show (5 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne6_1 : (6 : Kf) ≠ 1 := by
  intro h
  exact nz5 (show (5 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne2_3 : (2 : Kf) ≠ 3 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne3_2 : (3 : Kf) ≠ 2 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne2_4 : (2 : Kf) ≠ 4 := by
  intro h
  exact nz2 (show (2 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne4_2 : (4 : Kf) ≠ 2 := by
  intro h
  exact nz2 (show (2 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne2_5 : (2 : Kf) ≠ 5 := by
  intro h
  exact nz3 (show (3 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne5_2 : (5 : Kf) ≠ 2 := by
  intro h
  exact nz3 (show (3 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne2_6 : (2 : Kf) ≠ 6 := by
  intro h
  exact nz4 (show (4 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne6_2 : (6 : Kf) ≠ 2 := by
  intro h
  exact nz4 (show (4 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne3_4 : (3 : Kf) ≠ 4 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne4_3 : (4 : Kf) ≠ 3 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne3_5 : (3 : Kf) ≠ 5 := by
  intro h
  exact nz2 (show (2 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne5_3 : (5 : Kf) ≠ 3 := by
  intro h
  exact nz2 (show (2 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne3_6 : (3 : Kf) ≠ 6 := by
  intro h
  exact nz3 (show (3 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne6_3 : (6 : Kf) ≠ 3 := by
  intro h
  exact nz3 (show (3 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne4_5 : (4 : Kf) ≠ 5 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne5_4 : (5 : Kf) ≠ 4 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne4_6 : (4 : Kf) ≠ 6 := by
  intro h
  exact nz2 (show (2 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne6_4 : (6 : Kf) ≠ 4 := by
  intro h
  exact nz2 (show (2 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

@[simp] theorem ne5_6 : (5 : Kf) ≠ 6 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -h)

@[simp] theorem ne6_5 : (6 : Kf) ≠ 5 := by
  intro h
  exact one_ne_zero (show (1 : Kf) = 0 by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h)

theorem nzs : (2 : Kf) ≠ 0 ∧ (3 : Kf) ≠ 0 ∧ (5 : Kf) ≠ 0 ∧ (4 : Kf) ≠ 0 ∧ (6 : Kf) ≠ 0 ∧ (8 : Kf) ≠ 0 ∧ (9 : Kf) ≠ 0 ∧ (10 : Kf) ≠ 0 ∧ (12 : Kf) ≠ 0 ∧ (15 : Kf) ≠ 0 ∧ (16 : Kf) ≠ 0 ∧ (18 : Kf) ≠ 0 ∧ (20 : Kf) ≠ 0 ∧ (24 : Kf) ≠ 0 ∧ (30 : Kf) ≠ 0 ∧ (32 : Kf) ≠ 0 ∧ (36 : Kf) ≠ 0 ∧ (40 : Kf) ≠ 0 ∧ (45 : Kf) ≠ 0 ∧ (48 : Kf) ≠ 0 ∧ (60 : Kf) ≠ 0 ∧ (64 : Kf) ≠ 0 ∧ (72 : Kf) ≠ 0 ∧ (96 : Kf) ≠ 0 ∧ (120 : Kf) ≠ 0 ∧ (144 : Kf) ≠ 0 ∧ (288 : Kf) ≠ 0 ∧ (128 : Kf) ≠ 0 ∧ (256 : Kf) ≠ 0 := ⟨nz2, nz3, nz5, nz4, nz6, nz8, nz9, nz10, nz12, nz15, nz16, nz18, nz20, nz24, nz30, nz32, nz36, nz40, nz45, nz48, nz60, nz64, nz72, nz96, nz120, nz144, nz288, nz128, nz256⟩

theorem zns : (0 : Kf) ≠ 2 ∧ (0 : Kf) ≠ 3 ∧ (0 : Kf) ≠ 5 ∧ (0 : Kf) ≠ 4 ∧ (0 : Kf) ≠ 6 ∧ (0 : Kf) ≠ 8 ∧ (0 : Kf) ≠ 9 ∧ (0 : Kf) ≠ 10 ∧ (0 : Kf) ≠ 12 ∧ (0 : Kf) ≠ 15 ∧ (0 : Kf) ≠ 16 ∧ (0 : Kf) ≠ 18 ∧ (0 : Kf) ≠ 20 ∧ (0 : Kf) ≠ 24 ∧ (0 : Kf) ≠ 30 ∧ (0 : Kf) ≠ 32 ∧ (0 : Kf) ≠ 36 ∧ (0 : Kf) ≠ 40 ∧ (0 : Kf) ≠ 45 ∧ (0 : Kf) ≠ 48 ∧ (0 : Kf) ≠ 60 ∧ (0 : Kf) ≠ 64 ∧ (0 : Kf) ≠ 72 ∧ (0 : Kf) ≠ 96 ∧ (0 : Kf) ≠ 120 ∧ (0 : Kf) ≠ 144 ∧ (0 : Kf) ≠ 288 ∧ (0 : Kf) ≠ 128 ∧ (0 : Kf) ≠ 256 := ⟨zn2, zn3, zn5, zn4, zn6, zn8, zn9, zn10, zn12, zn15, zn16, zn18, zn20, zn24, zn30, zn32, zn36, zn40, zn45, zn48, zn60, zn64, zn72, zn96, zn120, zn144, zn288, zn128, zn256⟩

theorem nes : (1 : Kf) ≠ 2 ∧ (2 : Kf) ≠ 1 ∧ (1 : Kf) ≠ 3 ∧ (3 : Kf) ≠ 1 ∧ (1 : Kf) ≠ 4 ∧ (4 : Kf) ≠ 1 ∧ (1 : Kf) ≠ 5 ∧ (5 : Kf) ≠ 1 ∧ (1 : Kf) ≠ 6 ∧ (6 : Kf) ≠ 1 ∧ (2 : Kf) ≠ 3 ∧ (3 : Kf) ≠ 2 ∧ (2 : Kf) ≠ 4 ∧ (4 : Kf) ≠ 2 ∧ (2 : Kf) ≠ 5 ∧ (5 : Kf) ≠ 2 ∧ (2 : Kf) ≠ 6 ∧ (6 : Kf) ≠ 2 ∧ (3 : Kf) ≠ 4 ∧ (4 : Kf) ≠ 3 ∧ (3 : Kf) ≠ 5 ∧ (5 : Kf) ≠ 3 ∧ (3 : Kf) ≠ 6 ∧ (6 : Kf) ≠ 3 ∧ (4 : Kf) ≠ 5 ∧ (5 : Kf) ≠ 4 ∧ (4 : Kf) ≠ 6 ∧ (6 : Kf) ≠ 4 ∧ (5 : Kf) ≠ 6 ∧ (6 : Kf) ≠ 5 := ⟨ne1_2, ne2_1, ne1_3, ne3_1, ne1_4, ne4_1, ne1_5, ne5_1, ne1_6, ne6_1, ne2_3, ne3_2, ne2_4, ne4_2, ne2_5, ne5_2, ne2_6, ne6_2, ne3_4, ne4_3, ne3_5, ne5_3, ne3_6, ne6_3, ne4_5, ne5_4, ne4_6, ne6_4, ne5_6, ne6_5⟩

theorem cast_two (c : ℕ) (hc : c ≤ 5) (e : (c : Kf) - 2 = 0) : c = 2 := by
  interval_cases c
  · norm_num at e
  · norm_num at e
  · rfl
  · norm_num at e
  · norm_num at e
  · norm_num at e

theorem cast_inj5 (a b : ℕ) (ha : a < 5) (hb : b < 5) (h : (a : Kf) = b) : a = b := by
  have h' : (a : Kf) - b = 0 := sub_eq_zero.mpr h
  interval_cases a <;> interval_cases b <;> first | rfl | (exfalso; norm_num at h')

theorem cast_succ_ne (a : ℕ) (ha : a < 5) : (a : Kf) + 1 ≠ 0 := by
  intro h
  interval_cases a <;> norm_num at h

noncomputable def Ii [Fact (∃ i : Kf, i ^ 2 = -1)] : Kf := Classical.choose (Fact.out : ∃ i : Kf, i ^ 2 = -1)

set_option maxHeartbeats 800000 in
theorem Ii_mul_Ii [Fact (∃ i : Kf, i ^ 2 = -1)] : ((Ii (Kf := Kf)) : Kf) * (Ii (Kf := Kf)) = -1 := by
  have h : ((Ii (Kf := Kf)) : Kf) ^ 2 = -1 := Classical.choose_spec (Fact.out : ∃ i : Kf, i ^ 2 = -1)
  rw [← h]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

theorem sum_emb_perm {n k : ℕ} (σ : Equiv.Perm (Fin k)) (F : (Fin k ↪ Fin n) → Kf) :
    ∑ i : Fin k ↪ Fin n, F (σ.toEmbedding.trans i) = ∑ i : Fin k ↪ Fin n, F i := by
  refine Fintype.sum_bijective (fun i => σ.toEmbedding.trans i)
    ⟨fun i i' h => ?_, fun i => ⟨σ.symm.toEmbedding.trans i, ?_⟩⟩ _ _ (fun i => rfl)
  · refine Function.Embedding.ext fun a => ?_
    have h' := DFunLike.congr_fun h (σ.symm a)
    simpa using h'
  · ext a
    simp

theorem sum_emb_succ {n k : ℕ} (Φ : Fin n → (Fin k → Fin n) → Kf) :
    ∑ i : Fin (k + 1) ↪ Fin n, Φ (i 0) (fun b => i b.succ) =
      ∑ e : Fin k ↪ Fin n, ∑ a ∈ univ.filter (fun a => ∀ b, e b ≠ a), Φ a e := by
  classical
  rw [← (Equiv.embeddingFinSucc k (Fin n)).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ => ?_
  symm
  rw [Finset.sum_subtype (p := fun a => a ∉ Set.range e) (univ.filter (fun a => ∀ b, e b ≠ a))
    (fun a => by simp [Set.mem_range]) (fun a => Φ a e)]
  refine Fintype.sum_congr _ _ fun a => ?_
  simp only [Equiv.coe_embeddingFinSucc_symm, Fin.cons_zero, Fin.cons_succ]

theorem rank_nullity {U V : Type} [AddCommGroup U] [Module Kf U] [FiniteDimensional Kf U]
    [AddCommGroup V] [Module Kf V] (L : Submodule Kf U) (f : U →ₗ[Kf] V) :
    Module.finrank Kf L = Module.finrank Kf (L ⊓ LinearMap.ker f : Submodule Kf U) +
      Module.finrank Kf (L.map f) := by
  have hrn : Module.finrank Kf (L.map f) +
      Module.finrank Kf (L ⊓ LinearMap.ker f : Submodule Kf U) = Module.finrank Kf L := by
    rw [← (Submodule.submoduleOfEquivInf _ _).finrank_eq,
      ← (f.submoduleMap L).finrank_range_add_finrank_ker,
      LinearMap.range_submoduleMap, LinearMap.ker_submoduleMap]
    simp
  omega

def sumZero (n : ℕ) : Submodule Kf (Fin n → Kf) :=
  LinearMap.ker (∑ i, (LinearMap.proj i : (Fin n → Kf) →ₗ[Kf] Kf))

theorem mem_sumZero {n : ℕ} (v : Fin n → Kf) : v ∈ (sumZero (Kf := Kf)) n ↔ ∑ i, v i = 0 := by
  simp [sumZero, LinearMap.sum_apply]

theorem finrank_sumZero {n : ℕ} (hn : 1 ≤ n) : Module.finrank Kf ((sumZero (Kf := Kf)) n) ≤ n - 1 := by
  have hne : (sumZero (Kf := Kf)) n ≠ ⊤ := by
    intro h
    have hm : (Pi.single (⟨0, hn⟩ : Fin n) (1 : Kf)) ∈ (sumZero (Kf := Kf)) n := h ▸ Submodule.mem_top
    rw [mem_sumZero] at hm
    simp at hm
  have := Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at this
  omega

theorem fin5 (P : Fin 5 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) :
    ∀ m, P m := by
  intro m
  fin_cases m
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

abbrev T4 := Fin 5 × Fin 5 × Fin 5 × Fin 5

def tup : T4 ≃ (Fin 4 → Fin 5) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  invFun z := (z 0, z 1, z 2, z 3)
  left_inv _ := rfl
  right_inv z := by
    ext i
    fin_cases i <;> rfl

theorem emb4 (F : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Kf) :
    ∑ e : Fin 4 ↪ Fin 5, F (e 0) (e 1) (e 2) (e 3) = ∑ j, ∑ l, ∑ m, ∑ n,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else F j l m n := by
  classical
  let u (z : Fin 4 → Fin 5) : Kf := F (z 0) (z 1) (z 2) (z 3)
  have A : ∑ e : Fin 4 ↪ Fin 5, F (e 0) (e 1) (e 2) (e 3) =
      ∑ z : Fin 4 → Fin 5, if Function.Injective z then u z else 0 := by
    let E := Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 5)
    change (∑ e : Fin 4 ↪ Fin 5, u e) = _
    rw [← E.sum_comp (fun e : Fin 4 ↪ Fin 5 => u e), ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) u).symm
  rw [A, ← tup.sum_comp (fun z => if Function.Injective z then u z else 0)]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => ?_
  let z := tup (a, b, c, d)
  have p : z 0 = a := rfl
  have q : z 1 = b := rfl
  have s : z 2 = c := rfl
  have t : z 3 = d := rfl
  have f : Function.Injective z ↔ ¬(a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) := by
    constructor
    · intro o
      have h (i j : Fin 4) (g : i ≠ j) : z i ≠ z j := fun h => g (o h)
      exact not_or_intro (h 0 1 (by decide)) (not_or_intro (h 0 2 (by decide))
        (not_or_intro (h 0 3 (by decide)) (not_or_intro (h 1 2 (by decide))
          (not_or_intro (h 1 3 (by decide)) (h 2 3 (by decide))))))
    · intro g i j v
      simp only [not_or] at g
      fin_cases i <;> fin_cases j <;> first | rfl | grind
  change (if Function.Injective z then u z else 0) = _
  by_cases g : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d
  · have k : ¬Function.Injective z := fun h => f.mp h g
    rw [if_neg k, if_pos g]
  · rw [if_pos (f.mpr g), if_neg g]
    rfl

def P4 (a : Fin 5) (N : (M45 Kf)) : Kf :=
  ∑ e : Fin 4 ↪ Fin 5, if (e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) then
    N (0, e 0) * N (1, e 1) * N (2, e 2) * N (3, e 3) else 0

theorem P4_eq (a : Fin 5) (N : (M45 Kf)) : P4 a N = ∑ j, ∑ l, ∑ m, ∑ n,
    if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
      if (j ≠ a ∧ l ≠ a ∧ m ≠ a ∧ n ≠ a) then N (0, j) * N (1, l) * N (2, m) * N (3, n) else 0 :=
  emb4 (fun j l m n => if (j ≠ a ∧ l ≠ a ∧ m ≠ a ∧ n ≠ a) then
    N (0, j) * N (1, l) * N (2, m) * N (3, n) else 0)

def SLev (K : Submodule Kf (M45 Kf)) : Prop :=
  ∀ Y ∈ K, ∀ a : Fin 5, P4 a (fun p => 1 + Y p) = 24

theorem perm5_row (r : Fin 5) (M : (M55 Kf)) :
    ∑ f : Fin 5 ↪ Fin 5, ∏ i, M (i, f i) =
      ∑ a, M (r, a) * P4 a (fun p => M (r.succAbove p.1, p.2)) := by
  have h1 : ∑ f : Fin 5 ↪ Fin 5, ∏ i, M (i, f i) =
      ∑ g : Fin 5 ↪ Fin 5, ∏ i, M (r.cycleRange.symm i, g i) := by
    refine Eq.trans ?_ (sum_emb_perm r.cycleRange.symm
      (fun g : Fin 5 ↪ Fin 5 => ∏ i, M (r.cycleRange.symm i, g i)))
    refine Finset.sum_congr rfl fun f _ => ?_
    exact (Equiv.prod_comp r.cycleRange.symm (fun j => M (j, f j))).symm
  have h2 : ∀ g : Fin 5 ↪ Fin 5, ∏ i, M (r.cycleRange.symm i, g i) =
      M (r, g 0) * ∏ b : Fin 4, M (r.succAbove b, g b.succ) := by
    intro g
    rw [Fin.prod_univ_succ]
    simp only [Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ]
  rw [h1]
  refine (Finset.sum_congr rfl (fun g _ => h2 g)).trans ?_
  refine (sum_emb_succ (fun a e => M (r, a) * ∏ b : Fin 4, M (r.succAbove b, e b))).trans ?_
  simp only [P4, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
  rw [Fin.prod_univ_four]
  by_cases h : ∀ b, e b ≠ a
  · rw [if_pos h, if_pos ⟨h 0, h 1, h 2, h 3⟩]
  · have h' : ¬(e 0 ≠ a ∧ e 1 ≠ a ∧ e 2 ≠ a ∧ e 3 ≠ a) := by
      intro hh
      apply h
      intro b
      fin_cases b
      · exact hh.1
      · exact hh.2.1
      · exact hh.2.2.1
      · exact hh.2.2.2
    rw [if_neg h, if_neg h', mul_zero]

def rowMat (r : Fin 5) (w : Fin 5 → Kf) : (M55 Kf) := fun p => if p.1 = r then w p.2 else 0

def del (r : Fin 5) : (M55 Kf) →ₗ[Kf] (M45 Kf) :=
  LinearMap.funLeft Kf Kf (fun p : Fin 4 × Fin 5 => (r.succAbove p.1, p.2))

def rowP (r : Fin 5) : (M55 Kf) →ₗ[Kf] (Fin 5 → Kf) :=
  LinearMap.funLeft Kf Kf (fun j : Fin 5 => (r, j))

theorem del_apply (r : Fin 5) (t : (M55 Kf)) (p : Fin 4 × Fin 5) :
    (del (Kf := Kf)) r t p = t (r.succAbove p.1, p.2) := rfl

theorem rowP_apply (r : Fin 5) (t : (M55 Kf)) (j : Fin 5) : (rowP (Kf := Kf)) r t j = t (r, j) := rfl

theorem level_row (L : Submodule Kf (M55 Kf))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (r : Fin 5) (hF : ∀ w : Fin 5 → Kf, ∑ j, w j = 0 → rowMat r w ∈ L)
    (y : (M55 Kf)) (hy : y ∈ L) (w : Fin 5 → Kf) (hw : ∑ j, w j = 0) (c : Kf) :
    ∑ a, (1 + c * y (r, a) + w a) * P4 a (fun p => 1 + c * y (r.succAbove p.1, p.2)) = 120 := by
  have hm : c • y + rowMat r w ∈ L := L.add_mem (L.smul_mem c hy) (hF w hw)
  have h := hL _ hm
  have h2 := perm5_row r (fun p => 1 + (c • y + rowMat r w) p)
  have h3 : ∑ a, (1 + (c • y + rowMat r w) (r, a)) *
      P4 a (fun p => 1 + (c • y + rowMat r w) (r.succAbove p.1, p.2)) = 120 := h2.symm.trans h
  rw [← h3]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e1 : (fun p : Fin 4 × Fin 5 => 1 + (c • y + rowMat r w) (r.succAbove p.1, p.2)) =
      fun p => 1 + c * y (r.succAbove p.1, p.2) := by
    funext p
    simp [rowMat, Fin.succAbove_ne]
  have e2 : (c • y + rowMat r w) (r, a) = c * y (r, a) + w a := by
    simp [rowMat]
  rw [e1, e2, add_assoc]

set_option maxHeartbeats 800000 in
theorem propR (L : Submodule Kf (M55 Kf))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (r : Fin 5) (hF : ∀ w : Fin 5 → Kf, ∑ j, w j = 0 → rowMat r w ∈ L)
    (y : (M55 Kf)) (hy : y ∈ L) :
    (∑ a, y (r, a) = 0) ∧ ∀ a, P4 a (fun p => 1 + y (r.succAbove p.1, p.2)) = 24 := by
  have base : ∀ c : Kf, ∑ a, (1 + c * y (r, a)) *
      P4 a (fun p => 1 + c * y (r.succAbove p.1, p.2)) = 120 := by
    intro c
    have h := level_row L hL r hF y hy (fun _ => 0) (by simp) c
    simpa using h
  have eqc : ∀ (c : Kf) (a b : Fin 5), P4 a (fun p => 1 + c * y (r.succAbove p.1, p.2)) =
      P4 b (fun p => 1 + c * y (r.succAbove p.1, p.2)) := by
    intro c a b
    have hw : ∑ j : Fin 5, ((if j = a then (1 : Kf) else 0) - (if j = b then (1 : Kf) else 0)) = 0 := by
      simp [Finset.sum_sub_distrib]
    have h := level_row L hL r hF y hy
      (fun j => (if j = a then (1 : Kf) else 0) - (if j = b then (1 : Kf) else 0)) hw c
    have h3 : ∑ x, (1 + c * y (r, x) + ((if x = a then (1 : Kf) else 0) - (if x = b then (1 : Kf) else 0))) *
        P4 x (fun p => 1 + c * y (r.succAbove p.1, p.2)) =
        ∑ x, (1 + c * y (r, x)) * P4 x (fun p => 1 + c * y (r.succAbove p.1, p.2)) +
        (P4 a (fun p => 1 + c * y (r.succAbove p.1, p.2)) -
          P4 b (fun p => 1 + c * y (r.succAbove p.1, p.2))) := by
      simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hb := base c
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h - hb - h3
  have key : ∀ c : Kf, (5 + c * ∑ a, y (r, a)) *
      P4 0 (fun p => 1 + c * y (r.succAbove p.1, p.2)) = 120 := by
    intro c
    have e5 : (5 : Kf) + c * ∑ a, y (r, a) = ∑ a : Fin 5, (1 + c * y (r, a)) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [← base c, e5, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [eqc c a 0]
  have hρ : ∑ a, y (r, a) = 0 := by
    by_contra hne
    have h := key (-5 / ∑ a, y (r, a))
    have e : (-5 / ∑ a, y (r, a)) * ∑ a, y (r, a) = -5 := by
      field_simp
    rw [e] at h
    apply (nz120 (Kf := Kf))
    rw [← h]
    ring
  refine ⟨hρ, fun a => ?_⟩
  have h := key 1
  rw [hρ] at h
  have h1 := eqc 1 a 0
  simp only [one_mul] at h h1
  rw [h1]
  linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 5 : Kf) * h

theorem stageA (L : Submodule Kf (M55 Kf))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (r : Fin 5) (hF : ∀ w : Fin 5 → Kf, ∑ j, w j = 0 → rowMat r w ∈ L) :
    SLev (L.map ((del (Kf := Kf)) r)) ∧
    SLev ((L ⊓ LinearMap.ker ((rowP (Kf := Kf)) r)).map ((del (Kf := Kf)) r)) ∧
    Module.finrank Kf L ≤
      4 + Module.finrank Kf ((L ⊓ LinearMap.ker ((rowP (Kf := Kf)) r) : Submodule Kf (M55 Kf)).map ((del (Kf := Kf)) r)) := by
  have hS : SLev (L.map ((del (Kf := Kf)) r)) := by
    intro Y hY a
    obtain ⟨y, hy, rfl⟩ := hY
    exact (propR L hL r hF y hy).2 a
  refine ⟨hS, ?_, ?_⟩
  · intro Y hY a
    exact hS Y (Submodule.map_mono inf_le_left hY) a
  · have h1 := rank_nullity L ((rowP (Kf := Kf)) r)
    have h2 : L.map ((rowP (Kf := Kf)) r) ≤ (sumZero (Kf := Kf)) 5 := by
      rintro v ⟨y, hy, rfl⟩
      rw [mem_sumZero]
      exact (propR L hL r hF y hy).1
    have h3 := (Submodule.finrank_mono h2).trans (finrank_sumZero (Kf := Kf) (n := 5) (by norm_num))
    have h4 := rank_nullity (L ⊓ LinearMap.ker ((rowP (Kf := Kf)) r) : Submodule Kf (M55 Kf)) ((del (Kf := Kf)) r)
    have h5 : ((L ⊓ LinearMap.ker ((rowP (Kf := Kf)) r)) ⊓ LinearMap.ker ((del (Kf := Kf)) r) : Submodule Kf (M55 Kf)) = ⊥ := by
      rw [eq_bot_iff]
      rintro t ⟨⟨_, ht1⟩, ht2⟩
      rw [Submodule.mem_bot]
      rw [SetLike.mem_coe, LinearMap.mem_ker] at ht1 ht2
      funext ⟨i, j⟩
      by_cases hi : i = r
      · have := congrFun ht1 j
        rw [rowP_apply] at this
        rw [hi]
        exact this
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hi
        have := congrFun ht2 (k, j)
        rw [del_apply] at this
        rw [← hk]
        exact this
    rw [h5, finrank_bot] at h4
    omega

def tau (z : (V4 Kf)) : Kf := z 0 + z 1 + z 2 + z 3

def ip (x y : (V4 Kf)) : Kf := x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

theorem FL_of (HSL : ∀ K : Submodule Kf (M45 Kf), SLev K → Module.finrank Kf K ≤ 3)
    (L : Submodule Kf (M55 Kf))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (r : Fin 5) (hF : ∀ w : Fin 5 → Kf, ∑ j, w j = 0 → rowMat r w ∈ L) :
    Module.finrank Kf L ≤ 7 := by
  obtain ⟨_, h2, h3⟩ := stageA L hL r hF
  have h4 := HSL _ h2
  omega

theorem emb_perm_bij : Function.Bijective (fun σ : Equiv.Perm (Fin 5) => σ.toEmbedding) :=
  ⟨fun σ τ h => Equiv.ext fun x => DFunLike.congr_fun h x,
    fun e => ⟨e.equivOfFiniteSelfEmbedding, e.toEmbedding_equivOfFiniteSelfEmbedding⟩⟩

theorem gap_swap5 (t : (M55 Kf)) :
    (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (f i, i))) =
      ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i)) := by
  have h1 : ∑ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (σ i, i)) =
      ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (f i, i)) :=
    Fintype.sum_bijective _ emb_perm_bij (fun σ : Equiv.Perm (Fin 5) => ∏ i, (1 + t (σ i, i)))
      (fun f : Fin 5 ↪ Fin 5 => ∏ i, (1 + t (f i, i))) (fun σ => rfl)
  have h2 : ∑ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (i, σ i)) =
      ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i)) :=
    Fintype.sum_bijective _ emb_perm_bij (fun σ : Equiv.Perm (Fin 5) => ∏ i, (1 + t (i, σ i)))
      (fun f : Fin 5 ↪ Fin 5 => ∏ i, (1 + t (i, f i))) (fun σ => rfl)
  have h3 : ∑ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (i, σ⁻¹ i)) =
      ∑ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (i, σ i)) :=
    Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin 5)))
      (fun σ : Equiv.Perm (Fin 5) => ∏ i, (1 + t (i, σ i)))
  have h4 : ∀ σ : Equiv.Perm (Fin 5), ∏ i, (1 + t (σ i, i)) = ∏ i, (1 + t (i, σ⁻¹ i)) := by
    intro σ
    exact Fintype.prod_equiv σ (fun i => 1 + t (σ i, i)) (fun j => 1 + t (j, σ⁻¹ j))
      (fun i => by simp)
  rw [← h1, ← h2, ← h3]
  exact Finset.sum_congr rfl (fun σ _ => h4 σ)

def trE5 : (M55 Kf) ≃ₗ[Kf] (M55 Kf) := LinearEquiv.funCongrLeft Kf Kf (Equiv.prodComm (Fin 5) (Fin 5))

def colMat (c : Fin 5) (w : Fin 5 → Kf) : (M55 Kf) := fun p => if p.2 = c then w p.1 else 0

theorem FL_col_of (HSL : ∀ K : Submodule Kf (M45 Kf), SLev K → Module.finrank Kf K ≤ 3)
    (L : Submodule Kf (M55 Kf))
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    (c : Fin 5) (hF : ∀ w : Fin 5 → Kf, ∑ j, w j = 0 → colMat c w ∈ L) :
    Module.finrank Kf L ≤ 7 := by
  have hL' : ∀ t ∈ L.map ((trE5 (Kf := Kf)) : (M55 Kf) →ₗ[Kf] (M55 Kf)),
      (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120 := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := gap_swap5 t
    have h2 : (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + ((trE5 (Kf := Kf)) t) (i, f i))) =
        ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (f i, i)) := rfl
    exact h2.trans (h1.trans (hL t ht))
  have hF' : ∀ w : Fin 5 → Kf, ∑ j, w j = 0 →
      rowMat c w ∈ L.map ((trE5 (Kf := Kf)) : (M55 Kf) →ₗ[Kf] (M55 Kf)) := by
    intro w hw
    refine ⟨colMat c w, hF w hw, ?_⟩
    funext ⟨i, j⟩
    rfl
  have h := FL_of HSL _ hL' c hF'
  have h2 := LinearEquiv.finrank_map_eq (trE5 (Kf := Kf)) L
  omega

def e2 (d : (V4 Kf)) : Kf := (tau d ^ 2 - ip d d) / 2

end

end PEqualNP.Outside.L_gct_210_aux.FLK

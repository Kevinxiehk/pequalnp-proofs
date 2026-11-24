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

def tau (z : (V4 Kf)) : Kf := z 0 + z 1 + z 2 + z 3

def ip (x y : (V4 Kf)) : Kf := x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def t3 (x y z : (V4 Kf)) : Kf := x 0 * y 0 * z 0 + x 1 * y 1 * z 1 + x 2 * y 2 * z 2 + x 3 * y 3 * z 3

def t4 (x y z w : (V4 Kf)) : Kf :=
  x 0 * y 0 * z 0 * w 0 + x 1 * y 1 * z 1 * w 1 + x 2 * y 2 * z 2 * w 2 + x 3 * y 3 * z 3 * w 3

def br (x y z w : (V4 Kf)) : Kf :=
  -6 * t4 x y z w + ip x y * ip z w + ip x z * ip y w + ip x w * ip y z

def col (N : (M45 Kf)) (m : Fin 5) : (V4 Kf) := fun i => N (i, m)

def pc (z1 z2 z3 z4 : (V4 Kf)) : Kf :=
  ∑ i, ∑ j, ∑ k, ∑ l, if i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l then 0
    else z1 i * z2 j * z3 k * z4 l

set_option maxHeartbeats 800000 in
theorem P4_c0 (N : (M45 Kf)) : P4 0 N = pc (col N 1) (col N 2) (col N 3) (col N 4) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem P4_c1 (N : (M45 Kf)) : P4 1 N = pc (col N 0) (col N 2) (col N 3) (col N 4) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem P4_c2 (N : (M45 Kf)) : P4 2 N = pc (col N 0) (col N 1) (col N 3) (col N 4) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem P4_c3 (N : (M45 Kf)) : P4 3 N = pc (col N 0) (col N 1) (col N 2) (col N 4) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem P4_c4 (N : (M45 Kf)) : P4 4 N = pc (col N 0) (col N 1) (col N 2) (col N 3) := by
  rw [P4_eq]
  simp (config := {decide := true}) only [pc, col, Fin.sum_univ_five, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

theorem sa0 : (0 : Fin 5).succAbove (0 : Fin 4) = 1 ∧ (0 : Fin 5).succAbove (1 : Fin 4) = 2 ∧
    (0 : Fin 5).succAbove (2 : Fin 4) = 3 ∧ (0 : Fin 5).succAbove (3 : Fin 4) = 4 := by decide

theorem sa1 : (1 : Fin 5).succAbove (0 : Fin 4) = 0 ∧ (1 : Fin 5).succAbove (1 : Fin 4) = 2 ∧
    (1 : Fin 5).succAbove (2 : Fin 4) = 3 ∧ (1 : Fin 5).succAbove (3 : Fin 4) = 4 := by decide

theorem sa2 : (2 : Fin 5).succAbove (0 : Fin 4) = 0 ∧ (2 : Fin 5).succAbove (1 : Fin 4) = 1 ∧
    (2 : Fin 5).succAbove (2 : Fin 4) = 3 ∧ (2 : Fin 5).succAbove (3 : Fin 4) = 4 := by decide

theorem sa3 : (3 : Fin 5).succAbove (0 : Fin 4) = 0 ∧ (3 : Fin 5).succAbove (1 : Fin 4) = 1 ∧
    (3 : Fin 5).succAbove (2 : Fin 4) = 2 ∧ (3 : Fin 5).succAbove (3 : Fin 4) = 4 := by decide

theorem sa4 : (4 : Fin 5).succAbove (0 : Fin 4) = 0 ∧ (4 : Fin 5).succAbove (1 : Fin 4) = 1 ∧
    (4 : Fin 5).succAbove (2 : Fin 4) = 2 ∧ (4 : Fin 5).succAbove (3 : Fin 4) = 3 := by decide

theorem P4_cols (m : Fin 5) (N : (M45 Kf)) : P4 m N = pc (col N (m.succAbove 0)) (col N (m.succAbove 1))
    (col N (m.succAbove 2)) (col N (m.succAbove 3)) := by
  revert m
  apply fin5
  · rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2]
    exact P4_c0 N
  · rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2]
    exact P4_c1 N
  · rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2]
    exact P4_c2 N
  · rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2]
    exact P4_c3 N
  · rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2]
    exact P4_c4 N

set_option maxHeartbeats 800000 in
theorem pc_tau (z1 z2 z3 z4 : (V4 Kf)) : pc z1 z2 z3 z4 =
    tau z1 * tau z2 * tau z3 * tau z4
    - (ip z1 z2 * tau z3 * tau z4 + ip z1 z3 * tau z2 * tau z4 + ip z1 z4 * tau z2 * tau z3
      + ip z2 z3 * tau z1 * tau z4 + ip z2 z4 * tau z1 * tau z3 + ip z3 z4 * tau z1 * tau z2)
    + 2 * (tau z1 * t3 z2 z3 z4 + tau z2 * t3 z1 z3 z4 + tau z3 * t3 z1 z2 z4
      + tau z4 * t3 z1 z2 z3)
    + br z1 z2 z3 z4 := by
  simp (config := {decide := true}) only [pc, tau, ip, t3, t4, br, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem pc_expand (z1 z2 z3 z4 : (V4 Kf)) (c : Kf) :
    pc (fun i => 1 + c * z1 i) (fun i => 1 + c * z2 i) (fun i => 1 + c * z3 i)
      (fun i => 1 + c * z4 i) =
    24 + c * (6 * (tau z1 + tau z2 + tau z3 + tau z4))
    + c ^ 2 * (2 * (tau z1 * tau z2 + tau z1 * tau z3 + tau z1 * tau z4 + tau z2 * tau z3
        + tau z2 * tau z4 + tau z3 * tau z4)
      - 2 * (ip z1 z2 + ip z1 z3 + ip z1 z4 + ip z2 z3 + ip z2 z4 + ip z3 z4))
    + c ^ 3 * ((tau z1 * tau z2 * tau z3 - tau z1 * ip z2 z3 - tau z2 * ip z1 z3
          - tau z3 * ip z1 z2 + 2 * t3 z1 z2 z3)
        + (tau z1 * tau z2 * tau z4 - tau z1 * ip z2 z4 - tau z2 * ip z1 z4
          - tau z4 * ip z1 z2 + 2 * t3 z1 z2 z4)
        + (tau z1 * tau z3 * tau z4 - tau z1 * ip z3 z4 - tau z3 * ip z1 z4
          - tau z4 * ip z1 z3 + 2 * t3 z1 z3 z4)
        + (tau z2 * tau z3 * tau z4 - tau z2 * ip z3 z4 - tau z3 * ip z2 z4
          - tau z4 * ip z2 z3 + 2 * t3 z2 z3 z4))
    + c ^ 4 * pc z1 z2 z3 z4 := by
  simp (config := {decide := true}) only [pc, tau, ip, t3, Fin.sum_univ_four,
    ite_true, ite_false, add_zero, zero_add]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem coeffs (z1 z2 z3 z4 : (V4 Kf))
    (h : ∀ c : Kf, pc (fun i => 1 + c * z1 i) (fun i => 1 + c * z2 i) (fun i => 1 + c * z3 i)
      (fun i => 1 + c * z4 i) = 24) :
    tau z1 + tau z2 + tau z3 + tau z4 = 0 ∧
    (2 * (tau z1 * tau z2 + tau z1 * tau z3 + tau z1 * tau z4 + tau z2 * tau z3
        + tau z2 * tau z4 + tau z3 * tau z4)
      - 2 * (ip z1 z2 + ip z1 z3 + ip z1 z4 + ip z2 z3 + ip z2 z4 + ip z3 z4) = 0) ∧
    ((tau z1 * tau z2 * tau z3 - tau z1 * ip z2 z3 - tau z2 * ip z1 z3
          - tau z3 * ip z1 z2 + 2 * t3 z1 z2 z3)
        + (tau z1 * tau z2 * tau z4 - tau z1 * ip z2 z4 - tau z2 * ip z1 z4
          - tau z4 * ip z1 z2 + 2 * t3 z1 z2 z4)
        + (tau z1 * tau z3 * tau z4 - tau z1 * ip z3 z4 - tau z3 * ip z1 z4
          - tau z4 * ip z1 z3 + 2 * t3 z1 z3 z4)
        + (tau z2 * tau z3 * tau z4 - tau z2 * ip z3 z4 - tau z3 * ip z2 z4
          - tau z4 * ip z2 z3 + 2 * t3 z2 z3 z4) = 0) ∧
    pc z1 z2 z3 z4 = 0 := by
  have e1 := h 1
  have e2 := h (-1)
  have e3 := h 2
  have e4 := h (-2)
  rw [pc_expand] at e1 e2 e3 e4
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 9 : Kf) * (e1 - e2) - (1 / 72 : Kf) * (e3 - e4)
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (2 / 3 : Kf) * (e1 + e2) - (1 / 24 : Kf) * (e3 + e4)
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 12 : Kf) * (e3 - e4) - (1 / 6 : Kf) * (e1 - e2)
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 24 : Kf) * (e3 + e4) - (1 / 6 : Kf) * (e1 + e2)

set_option maxHeartbeats 800000 in
theorem coeffs0 (z1 z2 z3 z4 : (V4 Kf))
    (h : ∀ c : Kf, pc (fun i => 1 + c * z1 i) (fun i => 1 + c * z2 i) (fun i => 1 + c * z3 i)
      (fun i => 1 + c * z4 i) = 24)
    (h1 : tau z1 = 0) (h2 : tau z2 = 0) (h3 : tau z3 = 0) (h4 : tau z4 = 0) :
    ip z1 z2 + ip z1 z3 + ip z1 z4 + ip z2 z3 + ip z2 z4 + ip z3 z4 = 0 ∧
    t3 z1 z2 z3 + t3 z1 z2 z4 + t3 z1 z3 z4 + t3 z2 z3 z4 = 0 ∧
    br z1 z2 z3 z4 = 0 := by
  obtain ⟨_, a2, a3, a4⟩ := coeffs z1 z2 z3 z4 h
  rw [pc_tau] at a4
  rw [h1, h2, h3, h4] at a2 a3 a4
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 2 : Kf) * a2
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * a3
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a4

theorem sl_cols (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Y : (M45 Kf)) (hY : Y ∈ K) (m : Fin 5) (c : Kf) :
    pc (fun i => 1 + c * col Y (m.succAbove 0) i) (fun i => 1 + c * col Y (m.succAbove 1) i)
      (fun i => 1 + c * col Y (m.succAbove 2) i) (fun i => 1 + c * col Y (m.succAbove 3) i) = 24 := by
  have h := hK (c • Y) (K.smul_mem c hY) m
  rw [P4_cols] at h
  exact h

def rs : (M45 Kf) →ₗ[Kf] (V4 Kf) :=
  LinearMap.pi fun i => ∑ j, LinearMap.proj (i, j)

theorem rs_apply (Y : (M45 Kf)) (i : Fin 4) :
    (rs (Kf := Kf)) Y i = Y (i, 0) + Y (i, 1) + Y (i, 2) + Y (i, 3) + Y (i, 4) := by
  simp [rs, LinearMap.sum_apply, Fin.sum_univ_five]

set_option maxHeartbeats 800000 in
theorem C1 (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Y : (M45 Kf)) (hY : Y ∈ K) :
    ∀ m, tau (col Y m) = 0 := by
  have a0 := (coeffs _ _ _ _ (sl_cols K hK Y hY 0)).1
  have a1 := (coeffs _ _ _ _ (sl_cols K hK Y hY 1)).1
  have a2 := (coeffs _ _ _ _ (sl_cols K hK Y hY 2)).1
  have a3 := (coeffs _ _ _ _ (sl_cols K hK Y hY 3)).1
  have a4 := (coeffs _ _ _ _ (sl_cols K hK Y hY 4)).1
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at a0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at a1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at a2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at a3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at a4
  apply fin5
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (a0 + a1 + a2 + a3 + a4) - a0
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (a0 + a1 + a2 + a3 + a4) - a1
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (a0 + a1 + a2 + a3 + a4) - a2
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (a0 + a1 + a2 + a3 + a4) - a3
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (a0 + a1 + a2 + a3 + a4) - a4

theorem C34 (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Y : (M45 Kf)) (hY : Y ∈ K) (m : Fin 5) :
    ip (col Y (m.succAbove 0)) (col Y (m.succAbove 1))
      + ip (col Y (m.succAbove 0)) (col Y (m.succAbove 2))
      + ip (col Y (m.succAbove 0)) (col Y (m.succAbove 3))
      + ip (col Y (m.succAbove 1)) (col Y (m.succAbove 2))
      + ip (col Y (m.succAbove 1)) (col Y (m.succAbove 3))
      + ip (col Y (m.succAbove 2)) (col Y (m.succAbove 3)) = 0 ∧
    t3 (col Y (m.succAbove 0)) (col Y (m.succAbove 1)) (col Y (m.succAbove 2))
      + t3 (col Y (m.succAbove 0)) (col Y (m.succAbove 1)) (col Y (m.succAbove 3))
      + t3 (col Y (m.succAbove 0)) (col Y (m.succAbove 2)) (col Y (m.succAbove 3))
      + t3 (col Y (m.succAbove 1)) (col Y (m.succAbove 2)) (col Y (m.succAbove 3)) = 0 ∧
    br (col Y (m.succAbove 0)) (col Y (m.succAbove 1)) (col Y (m.succAbove 2))
      (col Y (m.succAbove 3)) = 0 :=
  coeffs0 _ _ _ _ (sl_cols K hK Y hY m) (C1 K hK Y hY _) (C1 K hK Y hY _) (C1 K hK Y hY _)
    (C1 K hK Y hY _)

set_option maxHeartbeats 800000 in
theorem C2 (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Y : (M45 Kf)) (hY : Y ∈ K) :
    ∀ m, ip (col Y m) (col Y m) = ip ((rs (Kf := Kf)) Y) (col Y m) := by
  have b0 := (C34 K hK Y hY 0).1
  have b1 := (C34 K hK Y hY 1).1
  have b2 := (C34 K hK Y hY 2).1
  have b3 := (C34 K hK Y hY 3).1
  have b4 := (C34 K hK Y hY 4).1
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at b0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at b1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at b2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at b3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at b4
  simp only [ip, col] at b0 b1 b2 b3 b4
  apply fin5
  · simp only [ip, col, rs_apply]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) b0 - (1 / 3 : Kf) * (b0 + b1 + b2 + b3 + b4)
  · simp only [ip, col, rs_apply]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) b1 - (1 / 3 : Kf) * (b0 + b1 + b2 + b3 + b4)
  · simp only [ip, col, rs_apply]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) b2 - (1 / 3 : Kf) * (b0 + b1 + b2 + b3 + b4)
  · simp only [ip, col, rs_apply]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) b3 - (1 / 3 : Kf) * (b0 + b1 + b2 + b3 + b4)
  · simp only [ip, col, rs_apply]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) b4 - (1 / 3 : Kf) * (b0 + b1 + b2 + b3 + b4)

set_option maxHeartbeats 800000 in
theorem C2pol (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Y Y' : (M45 Kf)) (hY : Y ∈ K) (hY' : Y' ∈ K)
    (m : Fin 5) :
    2 * ip (col Y m) (col Y' m) = ip ((rs (Kf := Kf)) Y) (col Y' m) + ip ((rs (Kf := Kf)) Y') (col Y m) := by
  have e1 := C2 K hK Y hY m
  have e2 := C2 K hK Y' hY' m
  have e3 := C2 K hK (Y + Y') (K.add_mem hY hY') m
  rw [map_add] at e3
  simp only [ip, col, Pi.add_apply] at e1 e2 e3 ⊢
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) e3 - e1 - e2

def colL (m : Fin 5) : (M45 Kf) →ₗ[Kf] (V4 Kf) := LinearMap.funLeft Kf Kf (fun i : Fin 4 => (i, m))

def phi (m : Fin 5) : (M45 Kf) →ₗ[Kf] (V4 Kf) := (2 : Kf) • (colL (Kf := Kf)) m - (rs (Kf := Kf))

theorem phi_apply (m : Fin 5) (Y : (M45 Kf)) (i : Fin 4) : (phi (Kf := Kf)) m Y i = 2 * Y (i, m) - (rs (Kf := Kf)) Y i := rfl

theorem mem_Vs (v : (V4 Kf)) : v ∈ (sumZero (Kf := Kf)) 4 ↔ tau v = 0 := by
  rw [mem_sumZero, tau, Fin.sum_univ_four]

set_option maxHeartbeats 800000 in
theorem tau_rs (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Y : (M45 Kf)) (hY : Y ∈ K) : tau ((rs (Kf := Kf)) Y) = 0 := by
  have h0 := C1 K hK Y hY 0
  have h1 := C1 K hK Y hY 1
  have h2 := C1 K hK Y hY 2
  have h3 := C1 K hK Y hY 3
  have h4 := C1 K hK Y hY 4
  simp only [tau, col] at h0 h1 h2 h3 h4
  simp only [tau, rs_apply]
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h0 + h1 + h2 + h3 + h4

theorem map_rs_le (K : Submodule Kf (M45 Kf)) (hK : SLev K) : K.map (rs (Kf := Kf)) ≤ (sumZero (Kf := Kf)) 4 := by
  rintro _ ⟨Y, hY, rfl⟩
  rw [mem_Vs]
  exact tau_rs K hK Y hY

set_option maxHeartbeats 800000 in
theorem tau_phi (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Y : (M45 Kf)) (hY : Y ∈ K) (m : Fin 5) :
    tau ((phi (Kf := Kf)) m Y) = 0 := by
  have h1 := C1 K hK Y hY m
  have h2 := tau_rs K hK Y hY
  simp only [tau, col] at h1 h2
  simp only [tau, phi_apply]
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) 2 * h1 - h2

set_option maxHeartbeats 800000 in
theorem ip_phi (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Y Y' : (M45 Kf)) (hY : Y ∈ K) (hY' : Y' ∈ K)
    (m : Fin 5) : ip ((phi (Kf := Kf)) m Y) ((phi (Kf := Kf)) m Y') = ip ((rs (Kf := Kf)) Y) ((rs (Kf := Kf)) Y') := by
  have e := C2pol K hK Y Y' hY hY' m
  simp only [ip, col] at e
  simp only [ip, phi_apply]
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) 2 * e

set_option maxHeartbeats 800000 in
theorem ip_col_phi (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Z Y : (M45 Kf)) (hZ : Z ∈ K) (hY : Y ∈ K)
    (hZ0 : (rs (Kf := Kf)) Z = 0) (m : Fin 5) : ip (col Z m) ((phi (Kf := Kf)) m Y) = 0 := by
  have e := C2pol K hK Z Y hZ hY m
  rw [hZ0] at e
  simp only [ip, col, Pi.zero_apply] at e
  simp only [ip, col, phi_apply]
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) e

set_option maxHeartbeats 800000 in
theorem nondeg (x : (V4 Kf)) (hx : tau x = 0) (h : ∀ v : (V4 Kf), tau v = 0 → ip x v = 0) : x = 0 := by
  have a1 : x 0 * 1 + x 1 * (-1) + x 2 * 0 + x 3 * 0 = 0 :=
    h ![1, -1, 0, 0] (by norm_num [tau])
  have a2 : x 0 * 0 + x 1 * 1 + x 2 * (-1) + x 3 * 0 = 0 :=
    h ![0, 1, -1, 0] (by norm_num [tau])
  have a3 : x 0 * 0 + x 1 * 0 + x 2 * 1 + x 3 * (-1) = 0 :=
    h ![0, 0, 1, -1] (by norm_num [tau])
  unfold tau at hx
  funext i
  fin_cases i
  · show x 0 = 0
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hx + (3 / 4 : Kf) * a1 + (1 / 2 : Kf) * a2 + (1 / 4 : Kf) * a3
  · show x 1 = 0
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hx - (1 / 4 : Kf) * a1 + (1 / 2 : Kf) * a2 + (1 / 4 : Kf) * a3
  · show x 2 = 0
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hx - (1 / 4 : Kf) * a1 - (1 / 2 : Kf) * a2 + (1 / 4 : Kf) * a3
  · show x 3 = 0
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hx - (1 / 4 : Kf) * a1 - (1 / 2 : Kf) * a2 - (3 / 4 : Kf) * a3

theorem Bi (K : Submodule Kf (M45 Kf)) (hK : SLev K) (hq : Module.finrank Kf (K.map (rs (Kf := Kf))) = 3) :
    (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) = ⊥ := by
  have hV3 : Module.finrank Kf ((sumZero (Kf := Kf)) 4) ≤ 3 :=
    (finrank_sumZero (Kf := Kf) (n := 4) (by norm_num)).trans (by norm_num)
  have hS : K.map (rs (Kf := Kf)) ≤ (sumZero (Kf := Kf)) 4 := map_rs_le K hK
  have hSV : K.map (rs (Kf := Kf)) = (sumZero (Kf := Kf)) 4 :=
    Submodule.eq_of_le_of_finrank_le hS (le_trans hV3 (le_of_eq hq.symm))
  have hphi : ∀ m, K.map ((phi (Kf := Kf)) m) = (sumZero (Kf := Kf)) 4 := by
    intro m
    have hle : K.map ((phi (Kf := Kf)) m) ≤ (sumZero (Kf := Kf)) 4 := by
      rintro _ ⟨Y, hY, rfl⟩
      rw [mem_Vs]
      exact tau_phi K hK Y hY m
    have hker : (K ⊓ LinearMap.ker ((phi (Kf := Kf)) m) : Submodule Kf (M45 Kf)) ≤ K ⊓ LinearMap.ker (rs (Kf := Kf)) := by
      rintro Y ⟨hY, hY0⟩
      refine ⟨hY, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hY0 ⊢
      apply nondeg
      · exact tau_rs K hK Y hY
      · intro v hv
        have hv' : v ∈ K.map (rs (Kf := Kf)) := by
          rw [hSV, mem_Vs]
          exact hv
        obtain ⟨Y', hY', rfl⟩ := hv'
        rw [← ip_phi K hK Y Y' hY hY' m, hY0]
        simp [ip]
    have r1 := rank_nullity K ((phi (Kf := Kf)) m)
    have r2 := rank_nullity K (rs (Kf := Kf))
    have r3 := Submodule.finrank_mono hker
    have hP3 : 3 ≤ Module.finrank Kf (K.map ((phi (Kf := Kf)) m)) := by omega
    exact Submodule.eq_of_le_of_finrank_le hle (le_trans hV3 hP3)
  rw [eq_bot_iff]
  rintro Z ⟨hZ, hZ0⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hZ0
  rw [Submodule.mem_bot]
  have hcol : ∀ m, col Z m = 0 := by
    intro m
    apply nondeg
    · exact C1 K hK Z hZ m
    · intro v hv
      have hv' : v ∈ K.map ((phi (Kf := Kf)) m) := by
        rw [hphi m, mem_Vs]
        exact hv
      obtain ⟨Y, hY, rfl⟩ := hv'
      exact ip_col_phi K hK Z Y hZ hY hZ0 m
  funext ⟨i, j⟩
  exact congrFun (hcol j) i

set_option maxHeartbeats 800000 in
def dotDual : (V4 Kf) →ₗ[Kf] Module.Dual Kf (V4 Kf) :=
  LinearMap.mk₂ Kf (fun v z => ∑ i, v i * z i)
    (fun a b z => by simp only [Pi.add_apply, add_mul, sum_add_distrib])
    (fun c a z => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum])
    (fun v a b => by simp only [Pi.add_apply, mul_add, sum_add_distrib])
    (fun c v a => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ => by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf))

theorem dotDual_apply (v z : (V4 Kf)) : (dotDual (Kf := Kf)) v z = ∑ i, v i * z i := rfl

theorem dotDual_injective : Function.Injective (dotDual (Kf := Kf)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  funext j
  have h := LinearMap.congr_fun hv (Pi.single j 1)
  rw [dotDual_apply] at h
  simpa [Pi.single_apply] using h

theorem perp_bound (V W : Submodule Kf (V4 Kf)) (h : ∀ v ∈ V, ∀ z ∈ W, ∑ i, v i * z i = 0) :
    Module.finrank Kf V + Module.finrank Kf W ≤ Fintype.card (Fin 4) := by
  have hle : V.map (dotDual (Kf := Kf)) ≤ W.dualAnnihilator := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact h v hv z hz
  have e1 : Module.finrank Kf (V.map (dotDual (Kf := Kf))) = Module.finrank Kf V :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (dotDual_injective (Kf := Kf)) V)).symm
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have e3 := Submodule.finrank_mono hle
  rw [Module.finrank_fintype_fun_eq_card] at e2
  omega

set_option maxHeartbeats 800000 in
theorem Q1 (W : Submodule Kf (V4 Kf)) (hτ : ∀ x ∈ W, tau x = 0) (hI : ∀ x ∈ W, ∀ y ∈ W, ip x y = 0) :
    Module.finrank Kf W ≤ 1 := by
  have hone : (1 : (V4 Kf)) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hinf : W ⊓ Submodule.span Kf {(1 : (V4 Kf))} = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx1⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hx1
    obtain ⟨c, rfl⟩ := hx1
    have h := hτ _ hx
    have hc : c = 0 := by
      simp only [tau, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * h
    rw [hc, zero_smul]
    exact Submodule.zero_mem _
  have hperp : ∀ v ∈ W, ∀ z ∈ W ⊔ Submodule.span Kf {(1 : (V4 Kf))}, ∑ i, v i * z i = 0 := by
    intro v hv z hz
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have h1 := hI v hv w hw
    have h2 := hτ v hv
    simp only [ip, tau] at h1 h2
    simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h1 + c * h2
  have hb := perp_bound W (W ⊔ Submodule.span Kf {(1 : (V4 Kf))}) hperp
  have hs := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span Kf {(1 : (V4 Kf))})
  rw [hinf, finrank_bot, finrank_span_singleton hone] at hs
  rw [Fintype.card_fin] at hb
  omega

set_option maxHeartbeats 800000 in
theorem N_iso (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Z Z' : (M45 Kf))
    (hZ : Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)))
    (hZ' : Z' ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf))) (m : Fin 5) :
    ip (col Z m) (col Z' m) = 0 := by
  have hz := Submodule.mem_inf.mp hZ
  have hz' := Submodule.mem_inf.mp hZ'
  have e := C2pol K hK Z Z' hz.1 hz'.1 m
  rw [LinearMap.mem_ker.mp hz.2, LinearMap.mem_ker.mp hz'.2] at e
  simp only [ip, col, Pi.zero_apply] at e ⊢
  linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * e

set_option maxHeartbeats 800000 in
theorem finrank_sup_one (W : Submodule Kf (V4 Kf)) (hτ : ∀ x ∈ W, tau x = 0) :
    Module.finrank Kf (W ⊔ Submodule.span Kf {(1 : (V4 Kf))} : Submodule Kf (V4 Kf)) =
      Module.finrank Kf W + 1 := by
  have hone : (1 : (V4 Kf)) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hinf : W ⊓ Submodule.span Kf {(1 : (V4 Kf))} = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx1⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hx1
    obtain ⟨c, rfl⟩ := hx1
    have h := hτ _ hx
    have hc : c = 0 := by
      simp only [tau, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * h
    rw [hc, zero_smul]
    exact Submodule.zero_mem _
  have hs := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span Kf {(1 : (V4 Kf))})
  rw [hinf, finrank_bot, finrank_span_singleton hone] at hs
  omega

set_option maxHeartbeats 800000 in
theorem perp_sup_one (P W : Submodule Kf (V4 Kf)) (hP : ∀ p ∈ P, tau p = 0)
    (hW : ∀ w ∈ W, tau w = 0) (h : ∀ p ∈ P, ∀ w ∈ W, ip p w = 0) :
    Module.finrank Kf P + Module.finrank Kf W + 1 ≤ 4 := by
  have hperp : ∀ v ∈ P, ∀ z ∈ W ⊔ Submodule.span Kf {(1 : (V4 Kf))}, ∑ i, v i * z i = 0 := by
    intro v hv z hz
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have h1 := h v hv w hw
    have h2 := hP v hv
    simp only [ip, tau] at h1 h2
    simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h1 + c * h2
  have hb := perp_bound P (W ⊔ Submodule.span Kf {(1 : (V4 Kf))}) hperp
  have hs := finrank_sup_one W hW
  rw [Fintype.card_fin] at hb
  omega

set_option maxHeartbeats 800000 in
theorem Bii (K : Submodule Kf (M45 Kf)) (hK : SLev K) (hq : Module.finrank Kf (K.map (rs (Kf := Kf))) = 2)
    (hN : (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) ≠ ⊥) :
    ∃ u ∈ K.map (rs (Kf := Kf)), u ≠ 0 ∧ ∀ s ∈ K.map (rs (Kf := Kf)), ip u s = 0 := by
  by_contra hcon
  have hnd : ∀ u ∈ K.map (rs (Kf := Kf)), (∀ s ∈ K.map (rs (Kf := Kf)), ip u s = 0) → u = 0 := by
    intro u hu hs
    by_contra hne
    exact hcon ⟨u, hu, hne, hs⟩
  apply hN
  rw [eq_bot_iff]
  intro Z hZ
  rw [Submodule.mem_bot]
  have hz := Submodule.mem_inf.mp hZ
  have hZ0 : (rs (Kf := Kf)) Z = 0 := LinearMap.mem_ker.mp hz.2
  have hcol : ∀ m, col Z m = 0 := by
    intro m
    by_contra hzm
    have hker : (K ⊓ LinearMap.ker ((phi (Kf := Kf)) m) : Submodule Kf (M45 Kf)) ≤
        ((K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) ⊓ LinearMap.ker ((colL (Kf := Kf)) m) :
          Submodule Kf (M45 Kf)) := by
      intro Y hY
      have hy := Submodule.mem_inf.mp hY
      have hY0 : (phi (Kf := Kf)) m Y = 0 := LinearMap.mem_ker.mp hy.2
      have hrs : (rs (Kf := Kf)) Y = 0 := by
        apply hnd _ (Submodule.mem_map_of_mem hy.1)
        rintro _ ⟨Y', hY', rfl⟩
        rw [← ip_phi K hK Y Y' hy.1 hY' m, hY0]
        simp [ip]
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hy.1, LinearMap.mem_ker.mpr hrs⟩,
        LinearMap.mem_ker.mpr ?_⟩
      funext i
      have h1 := congrFun hY0 i
      rw [phi_apply, hrs] at h1
      simp only [Pi.zero_apply, sub_zero] at h1
      show Y (i, m) = 0
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * h1
    have r1 := rank_nullity K ((phi (Kf := Kf)) m)
    have r2 := rank_nullity K (rs (Kf := Kf))
    have r3 := rank_nullity (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) ((colL (Kf := Kf)) m)
    have r4 := Submodule.finrank_mono hker
    have r5 : 1 ≤ Module.finrank Kf ((K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)).map ((colL (Kf := Kf)) m)) := by
      by_contra h0
      have h00 : Module.finrank Kf
          ((K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)).map ((colL (Kf := Kf)) m)) = 0 := by omega
      rw [Submodule.finrank_eq_zero] at h00
      have hmem : col Z m ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)).map ((colL (Kf := Kf)) m) :=
        Submodule.mem_map_of_mem hZ
      rw [h00, Submodule.mem_bot] at hmem
      exact hzm hmem
    have hP3 : 3 ≤ Module.finrank Kf (K.map ((phi (Kf := Kf)) m)) := by omega
    have h1 : Module.finrank Kf (Submodule.span Kf {col Z m}) = 1 := finrank_span_singleton hzm
    have hb := perp_sup_one (K.map ((phi (Kf := Kf)) m)) (Submodule.span Kf {col Z m}) ?_ ?_ ?_
    · omega
    · rintro _ ⟨Y, hY, rfl⟩
      exact tau_phi K hK Y hY m
    · intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have ht := C1 K hK Z hz.1 m
      simp only [tau, Pi.smul_apply, smul_eq_mul] at ht ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) c * ht
    · rintro _ ⟨Y, hY, rfl⟩ w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have ht := ip_col_phi K hK Z Y hz.1 hY hZ0 m
      simp only [ip, Pi.smul_apply, smul_eq_mul] at ht ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) c * ht
  funext ⟨i, j⟩
  exact congrFun (hcol j) i

set_option maxHeartbeats 800000 in
theorem Q4 (v x : (V4 Kf)) (hv : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hx1 : tau x = 0)
    (hx2 : ip x x = 0) (hvx : ip v x = 0) : ∃ c : Kf, x = c • v := by
  have hW : Module.finrank Kf (Submodule.span Kf {v, x}) ≤ 1 := by
    apply Q1
    · intro a ha
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp ha
      simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv1 hx1 ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) s * hv1 + t * hx1
    · intro a ha b hb
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp ha
      obtain ⟨s', t', rfl⟩ := Submodule.mem_span_pair.mp hb
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv2 hx2 hvx ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) s * s' * hv2 + t * t' * hx2 + (s * t' + t * s') * hvx
  have hle : Submodule.span Kf {v} ≤ Submodule.span Kf {v, x} :=
    Submodule.span_mono (by simp)
  have h1 : Module.finrank Kf (Submodule.span Kf {v}) = 1 := finrank_span_singleton hv
  have heq := Submodule.eq_of_le_of_finrank_le hle (le_trans hW (le_of_eq h1.symm))
  have hx : x ∈ Submodule.span Kf {v} := by
    rw [heq]
    exact Submodule.subset_span (by simp)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨c, hc.symm⟩

theorem Biii (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Yu : (M45 Kf)) (hYu : Yu ∈ K)
    (hu : ip ((rs (Kf := Kf)) Yu) ((rs (Kf := Kf)) Yu) = 0) (Z : (M45 Kf))
    (hZ : Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)))
    (m : Fin 5) (hzm : col Z m ≠ 0) : ∃ c : Kf, (phi (Kf := Kf)) m Yu = c • col Z m := by
  have hz := Submodule.mem_inf.mp hZ
  apply Q4 (col Z m) ((phi (Kf := Kf)) m Yu) hzm (C1 K hK Z hz.1 m) (N_iso K hK Z Z hZ hZ m)
    (tau_phi K hK Yu hYu m)
  · rw [ip_phi K hK Yu Yu hYu hYu m]
    exact hu
  · exact ip_col_phi K hK Z Yu hz.1 hYu (LinearMap.mem_ker.mp hz.2) m

set_option maxHeartbeats 800000 in
theorem root4 (a b c d : Kf) (h1 : a + b + c + d = 0) (h2 : a * a + b * b + c * c + d * d = 0)
    (h3 : a * a * a + b * b * b + c * c * c + d * d * d = 0)
    (h4 : a * a * a * a + b * b * b * b + c * c * c * c + d * d * d * d = 0) : a = 0 := by
  have h : a ^ 4 = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]))
      (a ^ 3 - (a + b + c + d) / 2 * a ^ 2 + (a + b + c + d) ^ 2 / 6 * a
        - (a + b + c + d) ^ 3 / 24) * h1
      + (a ^ 2 / 2 - (a + b + c + d) / 2 * a + (a + b + c + d) ^ 2 / 4
        - (a * a + b * b + c * c + d * d) / 8) * h2
      + (a / 3 - (a + b + c + d) / 3) * h3 + (1 / 4 : Kf) * h4
  exact (pow_eq_zero_iff (by norm_num)).mp h

set_option maxHeartbeats 800000 in
theorem iso34 (v : (V4 Kf)) (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0)
    (h4 : t4 v v v v = 0) : v = 0 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 h4
  funext i
  fin_cases i
  · exact root4 (v 0) (v 1) (v 2) (v 3) h1 h2 h3 h4
  · exact root4 (v 1) (v 0) (v 2) (v 3) (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h1) (by linear_combination h2)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h3) (by linear_combination h4)
  · exact root4 (v 2) (v 0) (v 1) (v 3) (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h1) (by linear_combination h2)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h3) (by linear_combination h4)
  · exact root4 (v 3) (v 0) (v 1) (v 2) (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h1) (by linear_combination h2)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h3) (by linear_combination h4)

def indep (v w : (V4 Kf)) : Prop := ∀ s t : Kf, s • v + t • w = 0 → s = 0 ∧ t = 0

set_option maxHeartbeats 800000 in
theorem root4k (a b c d : Kf) (h1 : a + b + c + d = 0) (h2 : a * a + b * b + c * c + d * d = 0)
    (h3 : a * a * a + b * b * b + c * c * c + d * d * d = 0) :
    a ^ 4 = (a * a * a * a + b * b * b * b + c * c * c * c + d * d * d * d) / 4 := by
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]))
    (a ^ 3 - (a + b + c + d) / 2 * a ^ 2 + (a + b + c + d) ^ 2 / 6 * a
      - (a + b + c + d) ^ 3 / 24) * h1
    + (a ^ 2 / 2 - (a + b + c + d) / 2 * a + (a + b + c + d) ^ 2 / 4
      - (a * a + b * b + c * c + d * d) / 8) * h2
    + (a / 3 - (a + b + c + d) / 3) * h3

set_option maxHeartbeats 800000 in
theorem pow4_iso (w : (V4 Kf)) (h1 : tau w = 0) (h2 : ip w w = 0) (h3 : t3 w w w = 0) :
    w 0 ^ 4 = t4 w w w w / 4 ∧ w 1 ^ 4 = t4 w w w w / 4 ∧ w 2 ^ 4 = t4 w w w w / 4 ∧
      w 3 ^ 4 = t4 w w w w / 4 := by
  simp only [tau, ip, t3, t4] at h1 h2 h3 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) root4k (w 0) (w 1) (w 2) (w 3) h1 h2 h3
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) root4k (w 1) (w 0) (w 2) (w 3) (by linear_combination h1)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h2) (by linear_combination h3)
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) root4k (w 2) (w 0) (w 1) (w 3) (by linear_combination h1)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h2) (by linear_combination h3)
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) root4k (w 3) (w 0) (w 1) (w 2) (by linear_combination h1)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h2) (by linear_combination h3)

set_option maxHeartbeats 800000 in
theorem br_w3 (w : (V4 Kf)) (c P : Kf) (hw2 : ip w w = 0) (p0 : w 0 ^ 4 = P / 4)
    (p1 : w 1 ^ 4 = P / 4) (p2 : w 2 ^ 4 = P / 4) (p3 : w 3 ^ 4 = P / 4) :
    br (c • (fun i => w i ^ 3 : (V4 Kf))) (c • (fun i => w i ^ 3 : (V4 Kf))) w w = c ^ 2 * P ^ 2 / 2 := by
  simp only [br, t4, ip, Pi.smul_apply, smul_eq_mul] at hw2 ⊢
  linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-6 * c ^ 2) * ((w 0 ^ 4 + P / 4) * p0 + (w 1 ^ 4 + P / 4) * p1
      + (w 2 ^ 4 + P / 4) * p2 + (w 3 ^ 4 + P / 4) * p3)
    + 2 * c ^ 2 * (w 0 ^ 4 + w 1 ^ 4 + w 2 ^ 4 + w 3 ^ 4 + P) * (p0 + p1 + p2 + p3)
    + c ^ 2 * (w 0 ^ 6 + w 1 ^ 6 + w 2 ^ 6 + w 3 ^ 6) * hw2

set_option maxHeartbeats 800000 in
theorem G23core (v w : (V4 Kf)) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (hi : indep v w) (h3 : t3 w w w = 0) (h13 : t4 v w w w = 0) :
    br v v w w ≠ 0 := by
  have hw0 : w ≠ 0 := by
    intro h
    have := (hi 0 1 (by rw [h]; simp)).2
    exact one_ne_zero this
  have hv0 : v ≠ 0 := by
    intro h
    have := (hi 1 0 (by rw [h]; simp)).1
    exact one_ne_zero this
  have hP : t4 w w w w ≠ 0 := fun h => hw0 (iso34 w hw1 hw2 h3 h)
  obtain ⟨p0, p1, p2, p3⟩ := pow4_iso w hw1 hw2 h3
  have a1 : tau (fun i => w i ^ 3 : (V4 Kf)) = 0 := by
    simp only [tau, t3] at h3 ⊢
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h3
  have a2 : ip (fun i => w i ^ 3 : (V4 Kf)) (fun i => w i ^ 3 : (V4 Kf)) = 0 := by
    simp only [ip] at hw2 ⊢
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) w 0 ^ 2 * p0 + w 1 ^ 2 * p1 + w 2 ^ 2 * p2 + w 3 ^ 2 * p3
      + t4 w w w w / 4 * hw2
  have a3 : ip (fun i => w i ^ 3 : (V4 Kf)) v = 0 := by
    simp only [ip, t4] at h13 ⊢
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h13
  have a4 : (fun i => w i ^ 3 : (V4 Kf)) ≠ 0 := by
    intro h
    apply hP
    have e : t4 w w w w = ip w (fun i => w i ^ 3 : (V4 Kf)) := by
      simp only [t4, ip]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
    rw [e, h]
    simp [ip]
  obtain ⟨c, hc⟩ := Q4 (fun i => w i ^ 3 : (V4 Kf)) v a4 a1 a2 hv1 hv2 a3
  have hc0 : c ≠ 0 := by
    intro h
    apply hv0
    rw [hc, h, zero_smul]
  rw [hc, br_w3 w c (t4 w w w w) hw2 p0 p1 p2 p3]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 2 hP)) two_ne_zero

set_option maxHeartbeats 800000 in
theorem G23 (v w : (V4 Kf)) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hw1 : tau w = 0)
    (hw2 : ip w w = 0) (hi : indep v w) (μ ν1 ν2 ν3 : Kf) (hμ : μ ≠ 0) (h1 : ν1 ≠ 0)
    (h2 : ν2 ≠ 0) (h3 : ν3 ≠ 0)
    (hTa : t3 ((-μ) • v) (ν1 • w) (ν2 • w) + t3 ((-μ) • v) (ν1 • w) (ν3 • w)
      + t3 ((-μ) • v) (ν2 • w) (ν3 • w) + t3 (ν1 • w) (ν2 • w) (ν3 • w) = 0)
    (hTb : t3 (μ • v) (ν1 • w) (ν2 • w) + t3 (μ • v) (ν1 • w) (ν3 • w)
      + t3 (μ • v) (ν2 • w) (ν3 • w) + t3 (ν1 • w) (ν2 • w) (ν3 • w) = 0)
    (hBa : br ((-μ) • v) (ν1 • w) (ν2 • w) (ν3 • w) = 0)
    (hB1 : br (μ • v) ((-μ) • v) (ν2 • w) (ν3 • w) = 0) : False := by
  have hn : ν1 * ν2 * ν3 ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) h3
  have e1 : t3 w w w = 0 := by
    have h : ν1 * ν2 * ν3 * t3 w w w = 0 := by
      simp only [t3, Pi.smul_apply, smul_eq_mul] at hTa hTb ⊢
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * hTa + (1 / 2 : Kf) * hTb
    exact (mul_eq_zero.mp h).resolve_left hn
  have e2 : t4 v w w w = 0 := by
    have h : μ * (ν1 * ν2 * ν3) * t4 v w w w = 0 := by
      simp only [br, t4, ip, Pi.smul_apply, smul_eq_mul] at hBa hw2 ⊢
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 6 : Kf) * hBa + (1 / 2 : Kf) * μ * ν1 * ν2 * ν3
        * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3) * hw2
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hμ hn)
  have e3 : br v v w w = 0 := by
    have h : μ ^ 2 * (ν2 * ν3) * br v v w w = 0 := by
      simp only [br, t4, ip, Pi.smul_apply, smul_eq_mul] at hB1 ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * hB1
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (pow_ne_zero 2 hμ) (mul_ne_zero h2 h3))
  exact G23core v w hv1 hv2 hw1 hw2 hi e1 e2 e3

set_option maxHeartbeats 800000 in
theorem generic_t [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] {ι : Type} (s : Finset ι) (a b : ι → Kf) (h : ∀ i ∈ s, a i ≠ 0 ∨ b i ≠ 0) (hs : s.card ≤ 20) :
    ∃ t : Kf, ∀ i ∈ s, a i + t * b i ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := (Fact.out : ∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s) (s.image (fun i => -a i / b i))
    (Finset.card_image_le.trans hs)
  refine ⟨t, fun i hi h0 => ?_⟩
  by_cases hb : b i = 0
  · rw [hb, mul_zero, add_zero] at h0
    rcases h i hi with h1 | h1
    · exact h1 h0
    · exact h1 hb
  · apply ht
    rw [Finset.mem_image]
    refine ⟨i, hi, ?_⟩
    rw [div_eq_iff hb]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * h0

theorem generic_pt [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] {P : Type} [AddCommGroup P] [Module Kf P] {ι : Type} (s : Finset ι)
    (f : ι → P →ₗ[Kf] Kf) (h : ∀ i ∈ s, f i ≠ 0) (hs : s.card ≤ 20) : ∃ x : P, ∀ i ∈ s, f i x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => by simp at hi⟩
  | insert j s hj ih =>
    obtain ⟨x, hx⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      ((Finset.card_le_card (Finset.subset_insert j s)).trans hs)
    have hfj : f j ≠ 0 := h j (Finset.mem_insert_self j s)
    obtain ⟨y, hy⟩ : ∃ y, f j y ≠ 0 := by
      by_contra hcon
      apply hfj
      refine LinearMap.ext fun z => ?_
      by_contra hz
      exact hcon ⟨z, hz⟩
    obtain ⟨t, ht⟩ := generic_t (insert j s) (fun i => f i x) (fun i => f i y) (by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact Or.inr hy
      · exact Or.inl (hx i hi')) hs
    refine ⟨x + t • y, fun i hi => ?_⟩
    rw [map_add, map_smul, smul_eq_mul]
    exact ht i hi

def outer (v : (V4 Kf)) (x : Fin 5 → Kf) : (M45 Kf) := fun p => v p.1 * x p.2

set_option maxHeartbeats 800000 in
theorem A1facts (N : Submodule Kf (M45 Kf)) (hN : SLev N) (v : (V4 Kf)) (hv2 : ip v v = 0)
    (x : Fin 5 → Kf) (hZ : outer v x ∈ N) (m : Fin 5) :
    t3 v v v * (x (m.succAbove 0) * x (m.succAbove 1) * x (m.succAbove 2)
      + x (m.succAbove 0) * x (m.succAbove 1) * x (m.succAbove 3)
      + x (m.succAbove 0) * x (m.succAbove 2) * x (m.succAbove 3)
      + x (m.succAbove 1) * x (m.succAbove 2) * x (m.succAbove 3)) = 0 ∧
    t4 v v v v * (x (m.succAbove 0) * x (m.succAbove 1) * x (m.succAbove 2)
      * x (m.succAbove 3)) = 0 := by
  obtain ⟨_, c3, c4⟩ := C34 N hN _ hZ m
  simp only [t3, br, t4, ip, col, outer] at c3 c4 hv2 ⊢
  constructor
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) c3
  · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 6 : Kf) * c4 + (1 / 2 : Kf) * (x (m.succAbove 0) * x (m.succAbove 1)
      * x (m.succAbove 2) * x (m.succAbove 3)) * (v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3)
      * hv2

def lfN (N : Submodule Kf (M45 Kf)) (i0 : Fin 4) (j : Fin 5) : ↥N →ₗ[Kf] Kf :=
  (LinearMap.proj (i0, j)).comp N.subtype

theorem lfN_apply (N : Submodule Kf (M45 Kf)) (i0 : Fin 4) (j : Fin 5) (z : ↥N) :
    lfN N i0 j z = (z : (M45 Kf)) (i0, j) := rfl

def psiS (S : Finset (Fin 5)) (i0 : Fin 4) : (M45 Kf) →ₗ[Kf] (↥S → Kf) :=
  LinearMap.funLeft Kf Kf (fun j : ↥S => (i0, j.1))

set_option maxHeartbeats 800000 in
theorem A1 [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (v : (V4 Kf)) (hv : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hform : ∀ Z ∈ N, ∃ x : Fin 5 → Kf, Z = outer v x) : Module.finrank Kf N ≤ 2 := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 5), ∀ j, j ∈ S ↔ lfN N i0 j ≠ 0 := by
    classical
    exact ⟨Finset.univ.filter (fun j => lfN N i0 j ≠ 0), fun j => by simp⟩
  have hnS : ∀ j, j ∉ S → ∀ Z ∈ N, Z (i0, j) = 0 := by
    intro j hj Z hZ
    have h0 : lfN N i0 j = 0 := by
      by_contra h
      exact hj ((hS j).mpr h)
    exact LinearMap.congr_fun h0 ⟨Z, hZ⟩
  obtain ⟨z, hz⟩ := generic_pt S (lfN N i0) (fun j hj => (hS j).mp hj)
    ((Finset.card_le_univ S).trans (by simp))
  obtain ⟨x, hx⟩ := hform z.1 z.2
  have hZx : outer v x ∈ N := by
    rw [← hx]
    exact z.2
  have hxS : ∀ j, j ∈ S → x j ≠ 0 := by
    intro j hj h0
    apply hz j hj
    rw [lfN_apply, hx]
    simp [outer, h0]
  have hxnS : ∀ j, j ∉ S → x j = 0 := by
    intro j hj
    have h : outer v x (i0, j) = 0 := hnS j hj _ hZx
    simp only [outer] at h
    exact (mul_eq_zero.mp h).resolve_left hi0
  have hker : (N ⊓ LinearMap.ker ((psiS (Kf := Kf)) S i0) : Submodule Kf (M45 Kf)) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz' := Submodule.mem_inf.mp hZ
    obtain ⟨y, hy⟩ := hform Z hz'.1
    have hψ : (psiS (Kf := Kf)) S i0 Z = 0 := LinearMap.mem_ker.mp hz'.2
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h : Z (i0, j) = 0 := by
        by_cases hj : j ∈ S
        · exact congrFun hψ ⟨j, hj⟩
        · exact hnS j hj Z hz'.1
      rw [hy] at h
      simp only [outer] at h
      exact (mul_eq_zero.mp h).resolve_left hi0
    rw [hy]
    funext p
    simp [outer, hy0]
  have r := rank_nullity N ((psiS (Kf := Kf)) S i0)
  rw [hker, finrank_bot] at r
  have hle : Module.finrank Kf (N.map ((psiS (Kf := Kf)) S i0)) ≤ S.card := by
    have h := Submodule.finrank_le (N.map ((psiS (Kf := Kf)) S i0))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
    exact h
  have hsum : ∀ Z ∈ N, ∑ j : ↥S, Z (i0, j.1) = 0 := by
    intro Z hZ
    have h1 : ∑ j : ↥S, Z (i0, j.1) = ∑ j ∈ S, Z (i0, j) :=
      Finset.sum_coe_sort S (fun j => Z (i0, j))
    have h2 : ∑ j ∈ S, Z (i0, j) = ∑ j, Z (i0, j) :=
      Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hnS j hj Z hZ)
    have h3 := congrFun (hrs Z hZ) i0
    rw [rs_apply] at h3
    rw [h1, h2, Fin.sum_univ_five]
    exact h3
  have hlt : S.Nonempty → Module.finrank Kf (N.map ((psiS (Kf := Kf)) S i0)) < S.card := by
    rintro ⟨j0, hj0⟩
    have hsub : N.map ((psiS (Kf := Kf)) S i0) ≤
        LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → Kf) →ₗ[Kf] Kf)) := by
      rintro _ ⟨Z, hZ, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sum_apply]
      exact hsum Z hZ
    have hne' : LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → Kf) →ₗ[Kf] Kf)) ≠ ⊤ := by
      intro h
      have hm : (Pi.single (⟨j0, hj0⟩ : ↥S) (1 : Kf)) ∈
          LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → Kf) →ₗ[Kf] Kf)) :=
        h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sum_apply] at hm
      simp at hm
    have h1 := Submodule.finrank_lt hne'
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
    exact lt_of_le_of_lt (Submodule.finrank_mono hsub) h1
  by_cases h4 : t4 v v v v = 0
  · have h3 : t3 v v v ≠ 0 := fun h => hv (iso34 v hv1 hv2 h h4)
    have e0 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 0).1).resolve_left h3
    have e1 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 1).1).resolve_left h3
    have e2 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 2).1).resolve_left h3
    have e3 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 3).1).resolve_left h3
    have e4 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 4).1).resolve_left h3
    rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at e0
    rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at e1
    rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at e2
    rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at e3
    rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at e4
    have hs : x 0 + x 1 + x 2 + x 3 + x 4 = 0 := by
      have h := congrFun (hrs _ hZx) i0
      rw [rs_apply] at h
      simp only [outer, Pi.zero_apply] at h
      have h' : v i0 * (x 0 + x 1 + x 2 + x 3 + x 4) = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
      exact (mul_eq_zero.mp h').resolve_left hi0
    obtain ⟨s, hsdef⟩ : ∃ s : Kf, s = (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2) / 2 :=
      ⟨_, rfl⟩
    have cubic : ∀ j, x j ^ 3 = s * x j := by
      apply fin5
      · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e0
          + (x 0 ^ 2 - x 0 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 0 * hsdef
      · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e1
          + (x 1 ^ 2 - x 1 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 1 * hsdef
      · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e2
          + (x 2 ^ 2 - x 2 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 2 * hsdef
      · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e3
          + (x 3 ^ 2 - x 3 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 3 * hsdef
      · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e4
          + (x 4 ^ 2 - x 4 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 4 * hsdef
    have hsq : ∀ j, x j ^ 2 = if j ∈ S then s else 0 := by
      intro j
      by_cases hj : j ∈ S
      · rw [if_pos hj]
        apply mul_left_cancel₀ (hxS j hj)
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) cubic j
      · rw [if_neg hj, hxnS j hj]
        (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
    have hsum2 : ∑ j, x j ^ 2 = (S.card : Kf) * s := by
      rw [Finset.sum_congr rfl (fun j _ => hsq j), Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
    rw [Fin.sum_univ_five] at hsum2
    have hcard : S.card ≤ 2 := by
      rcases S.eq_empty_or_nonempty with h0 | ⟨j, hj⟩
      · rw [h0]
        simp
      · have hs0 : s ≠ 0 := by
          have h := hsq j
          rw [if_pos hj] at h
          rw [← h]
          exact pow_ne_zero 2 (hxS j hj)
        have h2 : ((S.card : Kf) - 2) * s = 0 := by
          linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * hsum2 - 2 * hsdef
        have h5 : (S.card : Kf) = 2 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hs0)
        have h6 : S.card = 2 := cast_two S.card ((Finset.card_le_univ S).trans (by simp)) (sub_eq_zero.mpr h5)
        omega
    omega
  · have hprod : ∀ m : Fin 5, ∃ k : Fin 4, m.succAbove k ∉ S := by
      intro m
      have h := (A1facts N hN v hv2 x hZx m).2
      have h' := (mul_eq_zero.mp h).resolve_left h4
      rcases mul_eq_zero.mp h' with h3 | h3
      · rcases mul_eq_zero.mp h3 with h2 | h2
        · rcases mul_eq_zero.mp h2 with h1 | h1
          · exact ⟨0, fun hin => hxS _ hin h1⟩
          · exact ⟨1, fun hin => hxS _ hin h1⟩
        · exact ⟨2, fun hin => hxS _ hin h2⟩
      · exact ⟨3, fun hin => hxS _ hin h3⟩
    obtain ⟨k1, hk1⟩ := hprod 0
    obtain ⟨k2, hk2⟩ := hprod ((0 : Fin 5).succAbove k1)
    have hne12 : ((0 : Fin 5).succAbove k1).succAbove k2 ≠ (0 : Fin 5).succAbove k1 :=
      Fin.succAbove_ne _ _
    have hc : S.card ≤ 3 := by
      have h1 := Finset.card_add_card_compl S
      have h2 : ({(0 : Fin 5).succAbove k1, ((0 : Fin 5).succAbove k1).succAbove k2} :
          Finset (Fin 5)) ⊆ Sᶜ := by
        intro j hj
        rw [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_compl]
        rcases hj with rfl | rfl
        · exact hk1
        · exact hk2
      have h3 := Finset.card_le_card h2
      rw [Finset.card_pair hne12.symm] at h3
      rw [Fintype.card_fin] at h1
      omega
    rcases S.eq_empty_or_nonempty with h0 | h0
    · have hc0 : S.card = 0 := by
        rw [h0]
        exact Finset.card_empty
      omega
    · have := hlt h0
      omega

theorem SLev_mono {N N' : Submodule Kf (M45 Kf)} (hN : SLev N) (h : N' ≤ N) : SLev N' :=
  fun Y hY a => hN Y (h hY) a

set_option maxHeartbeats 800000 in
theorem Niso (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (Z Z' : (M45 Kf))
    (hZ : Z ∈ N) (hZ' : Z' ∈ N) (m : Fin 5) : ip (col Z m) (col Z' m) = 0 := by
  have e := C2pol N hN Z Z' hZ hZ' m
  rw [hrs Z hZ, hrs Z' hZ'] at e
  simp only [ip, Pi.zero_apply] at e ⊢
  linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * e

theorem Ncol1 (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (m : Fin 5) :
    Module.finrank Kf (N.map ((colL (Kf := Kf)) m)) ≤ 1 := by
  apply Q1
  · rintro _ ⟨Z, hZ, rfl⟩
    exact C1 N hN Z hZ m
  · rintro _ ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩
    exact Niso N hN hrs Z Z' hZ hZ' m

theorem peel (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (m : Fin 5) :
    Module.finrank Kf N ≤
      1 + Module.finrank Kf (N ⊓ LinearMap.ker ((colL (Kf := Kf)) m) : Submodule Kf (M45 Kf)) := by
  have r := rank_nullity N ((colL (Kf := Kf)) m)
  have h := Ncol1 N hN hrs m
  omega

def efN (N : Submodule Kf (M45 Kf)) (p : Fin 4 × Fin 5) : ↥N →ₗ[Kf] Kf :=
  (LinearMap.proj p).comp N.subtype

theorem maxpt [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) :
    ∃ z ∈ N, ∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin 4 × Fin 5), ∀ p, p ∈ T ↔ efN N p ≠ 0 := by
    classical
    exact ⟨Finset.univ.filter (fun p => efN N p ≠ 0), fun p => by simp⟩
  obtain ⟨z, hz⟩ := generic_pt T (efN N) (fun p hp => (hT p).mp hp)
    ((Finset.card_le_univ T).trans (by simp))
  refine ⟨z.1, z.2, fun Z hZ m => ?_⟩
  by_cases h0 : col z.1 m = 0
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    funext i
    have hni : (i, m) ∉ T := by
      intro hin
      apply hz (i, m) hin
      exact congrFun h0 i
    have hf : efN N (i, m) = 0 := by
      by_contra h
      exact hni ((hT (i, m)).mpr h)
    exact LinearMap.congr_fun hf ⟨Z, hZ⟩
  · exact Q4 (col z.1 m) (col Z m) h0 (C1 N hN z.1 z.2 m) (Niso N hN hrs z.1 z.1 z.2 z.2 m)
      (C1 N hN Z hZ m) (Niso N hN hrs Z Z hZ hZ m) (Niso N hN hrs z.1 Z z.2 hZ m)

theorem perm_two {α : Type} [DecidableEq α] (i j a b : α) (c : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm α, σ i = a ∧ σ j = b := by
  have h : Equiv.swap i a b ≠ i := by
    intro e
    simpa [hab] using (congrArg (Equiv.swap i a) e).symm
  exact ⟨Equiv.swap i a * Equiv.swap j (Equiv.swap i a b),
    by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne c h.symm],
    by simp [Equiv.Perm.mul_apply]⟩

theorem perm_three (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by
  obtain ⟨σ1, h0, h1⟩ := perm_two (0 : Fin 5) 1 a b (by decide) hab
  have hc0 : (0 : Fin 5) ≠ σ1.symm c := by
    intro h
    apply hac
    rw [← h0, h, Equiv.apply_symm_apply]
  have hc1 : (1 : Fin 5) ≠ σ1.symm c := by
    intro h
    apply hbc
    rw [← h1, h, Equiv.apply_symm_apply]
  refine ⟨σ1 * Equiv.swap 2 (σ1.symm c), ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hc0, h0]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hc1, h1]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

theorem sum_cols_perm (σ : Equiv.Perm (Fin 5)) (Z : (M45 Kf)) :
    col Z (σ 0) + col Z (σ 1) + col Z (σ 2) + col Z (σ 3) + col Z (σ 4) = (rs (Kf := Kf)) Z := by
  have h : ∑ j, col Z (σ j) = ∑ j, col Z j := Equiv.sum_comp σ (fun j => col Z j)
  rw [Fin.sum_univ_five, Fin.sum_univ_five] at h
  rw [h]
  funext i
  simp only [Pi.add_apply, col, rs_apply]

theorem caseA3 (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (z : (M45 Kf))
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m) (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hind : ∀ s1 s2 s3 : Kf, s1 • col z a + s2 • col z b + s3 • col z c = 0 →
      s1 = 0 ∧ s2 = 0 ∧ s3 = 0) : Module.finrank Kf N ≤ 2 := by
  obtain ⟨σ, h0, h1, h2⟩ := perm_three a b c hab hac hbc
  have hN1 : SLev (N ⊓ LinearMap.ker ((colL (Kf := Kf)) (σ 3)) : Submodule Kf (M45 Kf)) :=
    (SLev_mono (Kf := Kf)) hN inf_le_left
  have hrs1 : ∀ Z ∈ (N ⊓ LinearMap.ker ((colL (Kf := Kf)) (σ 3)) : Submodule Kf (M45 Kf)), (rs (Kf := Kf)) Z = 0 :=
    fun Z hZ => hrs Z (Submodule.mem_inf.mp hZ).1
  have p1 := peel N hN hrs (σ 3)
  have p2 := peel _ hN1 hrs1 (σ 4)
  have hbot : ((N ⊓ LinearMap.ker ((colL (Kf := Kf)) (σ 3)) : Submodule Kf (M45 Kf)) ⊓
      LinearMap.ker ((colL (Kf := Kf)) (σ 4)) : Submodule Kf (M45 Kf)) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz2 := Submodule.mem_inf.mp hZ
    have hz1 := Submodule.mem_inf.mp hz2.1
    have hZN := hz1.1
    have c3 : col Z (σ 3) = 0 := LinearMap.mem_ker.mp hz1.2
    have c4 : col Z (σ 4) = 0 := LinearMap.mem_ker.mp hz2.2
    obtain ⟨s1, e1⟩ := hmax Z hZN a
    obtain ⟨s2, e2⟩ := hmax Z hZN b
    obtain ⟨s3, e3⟩ := hmax Z hZN c
    have hsum := sum_cols_perm σ Z
    rw [h0, h1, h2, c3, c4, hrs Z hZN, e1, e2, e3, add_zero, add_zero] at hsum
    obtain ⟨t1, t2, t3⟩ := hind s1 s2 s3 hsum
    have hcol : ∀ j, col Z (σ j) = 0 := by
      apply fin5
      · rw [h0, e1, t1, zero_smul]
      · rw [h1, e2, t2, zero_smul]
      · rw [h2, e3, t3, zero_smul]
      · exact c3
      · exact c4
    funext ⟨i, m⟩
    have hh := congrFun (hcol (σ.symm m)) i
    rw [Equiv.apply_symm_apply] at hh
    exact hh
  rw [hbot, finrank_bot] at p2
  omega

theorem caseLine [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (z : (M45 Kf))
    (hz : z ∈ N) (hmax : ∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m) (m0 : Fin 5)
    (hm0 : col z m0 ≠ 0) (hline : ∀ m, ∃ c : Kf, col z m = c • col z m0) :
    Module.finrank Kf N ≤ 2 := by
  have hform : ∀ Z ∈ N, ∃ x : Fin 5 → Kf, Z = outer (col z m0) x := by
    intro Z hZ
    have h : ∀ m, ∃ d : Kf, col Z m = d • col z m0 := by
      intro m
      obtain ⟨c, hc⟩ := hmax Z hZ m
      obtain ⟨c', hc'⟩ := hline m
      exact ⟨c * c', by rw [hc, hc', smul_smul]⟩
    choose x hx using h
    refine ⟨x, ?_⟩
    funext ⟨i, m⟩
    have hh := congrFun (hx m) i
    simp only [col, Pi.smul_apply, smul_eq_mul] at hh
    simp only [outer, col]
    rw [hh, mul_comm]
  exact A1 N hN hrs (col z m0) hm0 (C1 N hN z hz m0) (Niso N hN hrs z z hz hz m0) hform

def LemA2 : Prop :=
  ∀ N : Submodule Kf (M45 Kf), SLev N → (∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) → ∀ z ∈ N,
    (∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m) → ∀ a b : Fin 5,
    indep (col z a) (col z b) → (∀ m, ∃ s t : Kf, col z m = s • col z a + t • col z b) →
    Module.finrank Kf N ≤ 2

set_option maxHeartbeats 800000 in
theorem LemA_red [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] (H2 : (LemA2 (Kf := Kf))) (N : Submodule Kf (M45 Kf)) (hN : SLev N)
    (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) : Module.finrank Kf N ≤ 2 := by
  obtain ⟨z, hz, hmax⟩ := maxpt N hN hrs
  by_cases h2 : ∃ a b : Fin 5, indep (col z a) (col z b)
  · obtain ⟨a, b, hab⟩ := h2
    by_cases h3 : ∃ c : Fin 5, ∀ s1 s2 s3 : Kf,
        s1 • col z a + s2 • col z b + s3 • col z c = 0 → s1 = 0 ∧ s2 = 0 ∧ s3 = 0
    · obtain ⟨c, hc⟩ := h3
      have hne_ab : a ≠ b := by
        intro h
        have h1 := (hab 1 (-1) (by rw [h]; simp)).1
        exact one_ne_zero h1
      have hne_ac : a ≠ c := by
        intro h
        have h1 := (hc 1 0 (-1) (by rw [h]; simp)).1
        exact one_ne_zero h1
      have hne_bc : b ≠ c := by
        intro h
        have h1 := (hc 0 1 (-1) (by rw [h]; simp)).2.1
        exact one_ne_zero h1
      exact caseA3 N hN hrs z hmax a b c hne_ab hne_ac hne_bc hc
    · apply H2 N hN hrs z hz hmax a b hab
      intro m
      by_contra hcon
      apply h3
      refine ⟨m, fun s1 s2 s3 h => ?_⟩
      have hs3 : s3 = 0 := by
        by_contra hne
        apply hcon
        refine ⟨-s1 * s3⁻¹, -s2 * s3⁻¹, ?_⟩
        funext i
        have hi := congrFun h i
        have hinv := mul_inv_cancel₀ hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) s3⁻¹ * hi - col z m i * hinv
      rw [hs3, zero_smul, add_zero] at h
      obtain ⟨t1, t2⟩ := hab s1 s2 h
      exact ⟨t1, t2, hs3⟩
  · by_cases hall : ∀ m, col z m = 0
    · have hbot : N = ⊥ := by
        rw [eq_bot_iff]
        intro Z hZ
        rw [Submodule.mem_bot]
        funext ⟨i, m⟩
        obtain ⟨c, hc⟩ := hmax Z hZ m
        have hh := congrFun hc i
        rw [hall m] at hh
        simpa [col] using hh
      rw [hbot, finrank_bot]
      exact Nat.zero_le 2
    · obtain ⟨m0, hm0⟩ : ∃ m0, col z m0 ≠ 0 := by
        by_contra h
        apply hall
        intro m
        by_contra hm
        exact h ⟨m, hm⟩
      apply caseLine N hN hrs z hz hmax m0 hm0
      intro m
      by_contra hcon
      apply h2
      refine ⟨m0, m, fun s t h => ?_⟩
      have ht : t = 0 := by
        by_contra hne
        apply hcon
        refine ⟨-s * t⁻¹, ?_⟩
        funext i
        have hi := congrFun h i
        have hinv := mul_inv_cancel₀ hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) t⁻¹ * hi - col z m i * hinv
      rw [ht, zero_smul, add_zero] at h
      exact ⟨(smul_eq_zero.mp h).resolve_right hm0, ht⟩

def cperm (σ : Equiv.Perm (Fin 5)) : (M45 Kf) →ₗ[Kf] (M45 Kf) :=
  LinearMap.funLeft Kf Kf (fun p : Fin 4 × Fin 5 => (p.1, σ p.2))

theorem cperm_apply (σ : Equiv.Perm (Fin 5)) (Y : (M45 Kf)) (p : Fin 4 × Fin 5) :
    (cperm (Kf := Kf)) σ Y p = Y (p.1, σ p.2) := rfl

theorem P4_perm (σ : Equiv.Perm (Fin 5)) (a : Fin 5) (N : (M45 Kf)) :
    P4 a (fun p => N (p.1, σ p.2)) = P4 (σ a) N := by
  have h := (Equiv.embeddingCongr (Equiv.refl (Fin 4)) σ).sum_comp
    (fun e : Fin 4 ↪ Fin 5 => if (e 0 ≠ σ a ∧ e 1 ≠ σ a ∧ e 2 ≠ σ a ∧ e 3 ≠ σ a) then
      N (0, e 0) * N (1, e 1) * N (2, e 2) * N (3, e 3) else 0)
  unfold P4
  rw [← h]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [Equiv.embeddingCongr_apply]

theorem SLev_perm (σ : Equiv.Perm (Fin 5)) (N : Submodule Kf (M45 Kf)) (hN : SLev N) :
    SLev (N.map ((cperm (Kf := Kf)) σ)) := by
  intro Y hY a
  obtain ⟨Y0, hY0, rfl⟩ := hY
  have h := P4_perm σ a (fun p => 1 + Y0 p)
  exact h.trans (hN Y0 hY0 (σ a))

theorem pattern23 (N : Submodule Kf (M45 Kf)) (hN : SLev N) (z : (M45 Kf)) (hz : z ∈ N)
    (σ : Equiv.Perm (Fin 5)) (v w : (V4 Kf)) (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hw1 : tau w = 0) (hw2 : ip w w = 0) (hi : indep v w) (μ ν1 ν2 ν3 : Kf) (hμ : μ ≠ 0)
    (h1 : ν1 ≠ 0) (h2 : ν2 ≠ 0) (h3 : ν3 ≠ 0) (c0 : col z (σ 0) = μ • v)
    (c1 : col z (σ 1) = (-μ) • v) (c2 : col z (σ 2) = ν1 • w) (c3 : col z (σ 3) = ν2 • w)
    (c4 : col z (σ 4) = ν3 • w) : False := by
  have hNσ := SLev_perm σ N hN
  have hzσ : (cperm (Kf := Kf)) σ z ∈ N.map ((cperm (Kf := Kf)) σ) := Submodule.mem_map_of_mem hz
  have k0 := C34 _ hNσ _ hzσ 0
  have k1 := C34 _ hNσ _ hzσ 1
  have k2 := C34 _ hNσ _ hzσ 2
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at k0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at k1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at k2
  have d0 : col ((cperm (Kf := Kf)) σ z) 0 = μ • v := c0
  have d1 : col ((cperm (Kf := Kf)) σ z) 1 = (-μ) • v := c1
  have d2 : col ((cperm (Kf := Kf)) σ z) 2 = ν1 • w := c2
  have d3 : col ((cperm (Kf := Kf)) σ z) 3 = ν2 • w := c3
  have d4 : col ((cperm (Kf := Kf)) σ z) 4 = ν3 • w := c4
  rw [d1, d2, d3, d4] at k0
  rw [d0, d2, d3, d4] at k1
  rw [d0, d1, d3, d4] at k2
  exact G23 v w hv1 hv2 hw1 hw2 hi μ ν1 ν2 ν3 hμ h1 h2 h3 k0.2.1 k1.2.1 k0.2.2 k2.2.2

theorem indep_symm {v w : (V4 Kf)} (h : indep v w) : indep w v := fun s t e => by
  have h1 := h t s (by rw [add_comm]; exact e)
  exact ⟨h1.2, h1.1⟩

theorem sum_cols (Z : (M45 Kf)) : ∑ m, col Z m = (rs (Kf := Kf)) Z := by
  funext i
  rw [Finset.sum_apply, Fin.sum_univ_five, rs_apply]
  rfl

theorem perm_four (a b c d : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c ∧ σ 3 = d := by
  obtain ⟨σ1, h0, h1, h2⟩ := perm_three a b c hab hac hbc
  have hd0 : (0 : Fin 5) ≠ σ1.symm d := by
    intro h
    apply had
    rw [← h0, h, Equiv.apply_symm_apply]
  have hd1 : (1 : Fin 5) ≠ σ1.symm d := by
    intro h
    apply hbd
    rw [← h1, h, Equiv.apply_symm_apply]
  have hd2 : (2 : Fin 5) ≠ σ1.symm d := by
    intro h
    apply hcd
    rw [← h2, h, Equiv.apply_symm_apply]
  refine ⟨σ1 * Equiv.swap 3 (σ1.symm d), ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hd0, h0]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hd1, h1]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hd2, h2]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

def swp : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem swp0 : swp 0 = 2 := by decide

theorem swp1 : swp 1 = 3 := by decide

theorem swp2 : swp 2 = 0 := by decide

theorem swp3 : swp 3 = 1 := by decide

theorem swp4 : swp 4 = 4 := by decide

set_option maxHeartbeats 800000 in
theorem LemA2_proof : (LemA2 (Kf := Kf)) := by
  intro N hN hrs z hz hmax a b hab hspan
  have hua1 := C1 N hN z hz a
  have hua2 := Niso N hN hrs z z hz hz a
  have hub1 := C1 N hN z hz b
  have hub2 := Niso N hN hrs z z hz hz b
  choose sc tc hst using hspan
  have hua0 : col z a ≠ 0 := by
    intro h
    have h1 := (hab 1 0 (by rw [h]; simp)).1
    exact one_ne_zero h1
  have hh : ip (col z a) (col z b) ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := Q4 (col z a) (col z b) hua0 hua1 hua2 hub1 hub2 h
    have h1 := (hab c (-1) (by rw [hc]; simp)).2
    norm_num at h1
  have F1 : ∀ m, sc m * tc m = 0 := by
    intro m
    have e := Niso N hN hrs z z hz hz m
    rw [hst m] at e
    have e2 : 2 * (sc m * tc m) * ip (col z a) (col z b) = 0 := by
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e hua2 hub2 ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) e - sc m ^ 2 * hua2 - tc m ^ 2 * hub2
    rcases mul_eq_zero.mp e2 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    · exact absurd h hh
  have F2a : sc a = 1 ∧ tc a = 0 := by
    have e := hst a
    have h := hab (sc a - 1) (tc a) (by
      funext i
      have hi := congrFun e i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * hi)
    exact ⟨sub_eq_zero.mp h.1, h.2⟩
  have F2b : sc b = 0 ∧ tc b = 1 := by
    have e := hst b
    have h := hab (sc b) (tc b - 1) (by
      funext i
      have hi := congrFun e i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * hi)
    exact ⟨h.1, sub_eq_zero.mp h.2⟩
  have F3 : (∑ m, sc m) = 0 ∧ (∑ m, tc m) = 0 := by
    apply hab
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e1 : ∑ m, col z m i = 0 := by
      have h := congrFun (sum_cols z) i
      rw [Finset.sum_apply, hrs z hz] at h
      exact h
    have e2 : ∑ m, col z m i = (∑ m, sc m) * col z a i + (∑ m, tc m) * col z b i := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h := congrFun (hst m) i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
    rw [← e2]
    exact e1
  obtain ⟨a', ha'a, hsa'⟩ : ∃ a', a' ≠ a ∧ sc a' ≠ 0 := by
    by_contra hcon
    have hz0 : ∀ m, m ≠ a → sc m = 0 := by
      intro m hm
      by_contra h
      exact hcon ⟨m, hm, h⟩
    have h1 : ∑ m, sc m = sc a :=
      Finset.sum_eq_single a (fun m _ hm => hz0 m hm) (fun h => absurd (Finset.mem_univ a) h)
    rw [F3.1, F2a.1] at h1
    exact zero_ne_one h1
  obtain ⟨b', hb'b, htb'⟩ : ∃ b', b' ≠ b ∧ tc b' ≠ 0 := by
    by_contra hcon
    have hz0 : ∀ m, m ≠ b → tc m = 0 := by
      intro m hm
      by_contra h
      exact hcon ⟨m, hm, h⟩
    have h1 : ∑ m, tc m = tc b :=
      Finset.sum_eq_single b (fun m _ hm => hz0 m hm) (fun h => absurd (Finset.mem_univ b) h)
    rw [F3.2, F2b.2] at h1
    exact zero_ne_one h1
  have hta' : tc a' = 0 := (mul_eq_zero.mp (F1 a')).resolve_left hsa'
  have hsb' : sc b' = 0 := (mul_eq_zero.mp (F1 b')).resolve_right htb'
  have hne_ab : a ≠ b := by
    intro h
    apply one_ne_zero (α := Kf)
    rw [← F2a.1, h, F2b.1]
  have hne_ab' : a ≠ b' := by
    intro h
    apply htb'
    rw [← h, F2a.2]
  have hne_a'b : a' ≠ b := by
    intro h
    apply hsa'
    rw [h, F2b.1]
  have hne_a'b' : a' ≠ b' := by
    intro h
    apply htb'
    rw [← h, hta']
  obtain ⟨σ, h0, h1, h2, h3⟩ := perm_four a a' b b' ha'a.symm hne_ab hne_ab' hne_a'b hne_a'b'
    hb'b.symm
  have hSs : sc a + sc a' + sc b + sc b' + sc (σ 4) = 0 := by
    have h : ∑ j, sc (σ j) = ∑ m, sc m := Equiv.sum_comp σ sc
    rw [Fin.sum_univ_five, F3.1, h0, h1, h2, h3] at h
    exact h
  have hSt : tc a + tc a' + tc b + tc b' + tc (σ 4) = 0 := by
    have h : ∑ j, tc (σ j) = ∑ m, tc m := Equiv.sum_comp σ tc
    rw [Fin.sum_univ_five, F3.2, h0, h1, h2, h3] at h
    exact h
  rw [F2a.1, F2b.1, hsb'] at hSs
  rw [F2a.2, F2b.2, hta'] at hSt
  have za : col z a' = sc a' • col z a := by
    rw [hst a', hta', zero_smul, add_zero]
  have zb : col z b' = tc b' • col z b := by
    rw [hst b', hsb', zero_smul, zero_add]
  by_cases hse : sc (σ 4) = 0
  · by_cases hte : tc (σ 4) = 0
    · have ze : col z (σ 4) = 0 := by
        rw [hst (σ 4), hse, hte, zero_smul, zero_smul, add_zero]
      have hN1 : SLev (N ⊓ LinearMap.ker ((colL (Kf := Kf)) a) : Submodule Kf (M45 Kf)) :=
        (SLev_mono (Kf := Kf)) hN inf_le_left
      have hrs1 : ∀ Z ∈ (N ⊓ LinearMap.ker ((colL (Kf := Kf)) a) : Submodule Kf (M45 Kf)), (rs (Kf := Kf)) Z = 0 :=
        fun Z hZ => hrs Z (Submodule.mem_inf.mp hZ).1
      have p1 := peel N hN hrs a
      have p2 := peel _ hN1 hrs1 b
      have hbot : ((N ⊓ LinearMap.ker ((colL (Kf := Kf)) a) : Submodule Kf (M45 Kf)) ⊓
          LinearMap.ker ((colL (Kf := Kf)) b) : Submodule Kf (M45 Kf)) = ⊥ := by
        rw [eq_bot_iff]
        intro Z hZ
        rw [Submodule.mem_bot]
        have hz2 := Submodule.mem_inf.mp hZ
        have hz1 := Submodule.mem_inf.mp hz2.1
        have hZN := hz1.1
        have ca : col Z a = 0 := LinearMap.mem_ker.mp hz1.2
        have cb : col Z b = 0 := LinearMap.mem_ker.mp hz2.2
        obtain ⟨k1, e1⟩ := hmax Z hZN a'
        obtain ⟨k2, e2⟩ := hmax Z hZN b'
        obtain ⟨k3, e3⟩ := hmax Z hZN (σ 4)
        rw [za] at e1
        rw [zb] at e2
        rw [ze, smul_zero] at e3
        have hsum := sum_cols_perm σ Z
        rw [h0, h1, h2, h3, hrs Z hZN, ca, cb, e1, e2, e3] at hsum
        have hk := hab (k1 * sc a') (k2 * tc b') (by
          funext i
          have hi := congrFun hsum i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
          linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hi)
        have hk1 : k1 = 0 := (mul_eq_zero.mp hk.1).resolve_right hsa'
        have hk2 : k2 = 0 := (mul_eq_zero.mp hk.2).resolve_right htb'
        have hcol : ∀ j, col Z (σ j) = 0 := by
          apply fin5
          · rw [h0]
            exact ca
          · rw [h1, e1, hk1, zero_smul]
          · rw [h2]
            exact cb
          · rw [h3, e2, hk2, zero_smul]
          · exact e3
        funext ⟨i, m⟩
        have hh2 := congrFun (hcol (σ.symm m)) i
        rw [Equiv.apply_symm_apply] at hh2
        exact hh2
      rw [hbot, finrank_bot] at p2
      omega
    · exfalso
      have hsa'1 : sc a' = -1 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hSs - hse
      have c0 : col z (σ 0) = (1 : Kf) • col z a := by rw [h0, one_smul]
      have c1 : col z (σ 1) = (-1 : Kf) • col z a := by rw [h1, za, hsa'1]
      have c2 : col z (σ 2) = (1 : Kf) • col z b := by rw [h2, one_smul]
      have c3 : col z (σ 3) = tc b' • col z b := by rw [h3, zb]
      have c4 : col z (σ 4) = tc (σ 4) • col z b := by
        rw [hst (σ 4), hse, zero_smul, zero_add]
      exact pattern23 N hN z hz σ (col z a) (col z b) hua1 hua2 hub1 hub2 hab 1 1 (tc b')
        (tc (σ 4)) one_ne_zero one_ne_zero htb' hte c0 c1 c2 c3 c4
  · exfalso
    have hte : tc (σ 4) = 0 := (mul_eq_zero.mp (F1 (σ 4))).resolve_left hse
    have htb'1 : tc b' = -1 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hSt - hte
    have c0 : col z ((σ * swp) 0) =
        (1 : Kf) • col z b := by
      rw [Equiv.Perm.mul_apply, swp0, h2, one_smul]
    have c1 : col z ((σ * swp) 1) =
        (-1 : Kf) • col z b := by
      rw [Equiv.Perm.mul_apply, swp1, h3, zb, htb'1]
    have c2 : col z ((σ * swp) 2) =
        (1 : Kf) • col z a := by
      rw [Equiv.Perm.mul_apply, swp2, h0, one_smul]
    have c3 : col z ((σ * swp) 3) =
        sc a' • col z a := by
      rw [Equiv.Perm.mul_apply, swp3, h1, za]
    have c4 : col z ((σ * swp) 4) =
        sc (σ 4) • col z a := by
      rw [Equiv.Perm.mul_apply, swp4, hst (σ 4), hte, zero_smul, add_zero]
    exact pattern23 N hN z hz (σ * swp) (col z b)
      (col z a) hub1 hub2 hua1 hua2 ((indep_symm (Kf := Kf)) hab) 1 1 (sc a') (sc (σ 4)) one_ne_zero
      one_ne_zero hsa' hse c0 c1 c2 c3 c4

theorem LemA_proof [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) :
    Module.finrank Kf N ≤ 2 :=
  LemA_red (LemA2_proof (Kf := Kf)) N hN hrs

set_option maxHeartbeats 800000 in
theorem A1b [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (v : (V4 Kf)) (hv : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hform : ∀ Z ∈ N, ∃ x : Fin 5 → Kf, Z = outer v x) (h3 : t3 v v v ≠ 0) :
    Module.finrank Kf N ≤ 1 := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 5), ∀ j, j ∈ S ↔ lfN N i0 j ≠ 0 := by
    classical
    exact ⟨Finset.univ.filter (fun j => lfN N i0 j ≠ 0), fun j => by simp⟩
  have hnS : ∀ j, j ∉ S → ∀ Z ∈ N, Z (i0, j) = 0 := by
    intro j hj Z hZ
    have h0 : lfN N i0 j = 0 := by
      by_contra h
      exact hj ((hS j).mpr h)
    exact LinearMap.congr_fun h0 ⟨Z, hZ⟩
  obtain ⟨z, hz⟩ := generic_pt S (lfN N i0) (fun j hj => (hS j).mp hj)
    ((Finset.card_le_univ S).trans (by simp))
  obtain ⟨x, hx⟩ := hform z.1 z.2
  have hZx : outer v x ∈ N := by
    rw [← hx]
    exact z.2
  have hxS : ∀ j, j ∈ S → x j ≠ 0 := by
    intro j hj h0
    apply hz j hj
    rw [lfN_apply, hx]
    simp [outer, h0]
  have hxnS : ∀ j, j ∉ S → x j = 0 := by
    intro j hj
    have h : outer v x (i0, j) = 0 := hnS j hj _ hZx
    simp only [outer] at h
    exact (mul_eq_zero.mp h).resolve_left hi0
  have hker : (N ⊓ LinearMap.ker ((psiS (Kf := Kf)) S i0) : Submodule Kf (M45 Kf)) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz' := Submodule.mem_inf.mp hZ
    obtain ⟨y, hy⟩ := hform Z hz'.1
    have hψ : (psiS (Kf := Kf)) S i0 Z = 0 := LinearMap.mem_ker.mp hz'.2
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h : Z (i0, j) = 0 := by
        by_cases hj : j ∈ S
        · exact congrFun hψ ⟨j, hj⟩
        · exact hnS j hj Z hz'.1
      rw [hy] at h
      simp only [outer] at h
      exact (mul_eq_zero.mp h).resolve_left hi0
    rw [hy]
    funext p
    simp [outer, hy0]
  have r := rank_nullity N ((psiS (Kf := Kf)) S i0)
  rw [hker, finrank_bot] at r
  have hle : Module.finrank Kf (N.map ((psiS (Kf := Kf)) S i0)) ≤ S.card := by
    have h := Submodule.finrank_le (N.map ((psiS (Kf := Kf)) S i0))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
    exact h
  have hsum : ∀ Z ∈ N, ∑ j : ↥S, Z (i0, j.1) = 0 := by
    intro Z hZ
    have h1 : ∑ j : ↥S, Z (i0, j.1) = ∑ j ∈ S, Z (i0, j) :=
      Finset.sum_coe_sort S (fun j => Z (i0, j))
    have h2 : ∑ j ∈ S, Z (i0, j) = ∑ j, Z (i0, j) :=
      Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hnS j hj Z hZ)
    have h3 := congrFun (hrs Z hZ) i0
    rw [rs_apply] at h3
    rw [h1, h2, Fin.sum_univ_five]
    exact h3
  have hlt : S.Nonempty → Module.finrank Kf (N.map ((psiS (Kf := Kf)) S i0)) < S.card := by
    rintro ⟨j0, hj0⟩
    have hsub : N.map ((psiS (Kf := Kf)) S i0) ≤
        LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → Kf) →ₗ[Kf] Kf)) := by
      rintro _ ⟨Z, hZ, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sum_apply]
      exact hsum Z hZ
    have hne' : LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → Kf) →ₗ[Kf] Kf)) ≠ ⊤ := by
      intro h
      have hm : (Pi.single (⟨j0, hj0⟩ : ↥S) (1 : Kf)) ∈
          LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → Kf) →ₗ[Kf] Kf)) :=
        h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sum_apply] at hm
      simp at hm
    have h1 := Submodule.finrank_lt hne'
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
    exact lt_of_le_of_lt (Submodule.finrank_mono hsub) h1
  have e0 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 0).1).resolve_left h3
  have e1 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 1).1).resolve_left h3
  have e2 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 2).1).resolve_left h3
  have e3 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 3).1).resolve_left h3
  have e4 := (mul_eq_zero.mp (A1facts N hN v hv2 x hZx 4).1).resolve_left h3
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at e0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at e1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at e2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at e3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at e4
  have hs : x 0 + x 1 + x 2 + x 3 + x 4 = 0 := by
    have h := congrFun (hrs _ hZx) i0
    rw [rs_apply] at h
    simp only [outer, Pi.zero_apply] at h
    have h' : v i0 * (x 0 + x 1 + x 2 + x 3 + x 4) = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
    exact (mul_eq_zero.mp h').resolve_left hi0
  obtain ⟨s, hsdef⟩ : ∃ s : Kf, s = (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2) / 2 :=
    ⟨_, rfl⟩
  have cubic : ∀ j, x j ^ 3 = s * x j := by
    apply fin5
    · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e0
        + (x 0 ^ 2 - x 0 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 0 * hsdef
    · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e1
        + (x 1 ^ 2 - x 1 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 1 * hsdef
    · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e2
        + (x 2 ^ 2 - x 2 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 2 * hsdef
    · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e3
        + (x 3 ^ 2 - x 3 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 3 * hsdef
    · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (e0 + e1 + e2 + e3 + e4) - e4
        + (x 4 ^ 2 - x 4 * (x 0 + x 1 + x 2 + x 3 + x 4) / 2) * hs - x 4 * hsdef
  have hsq : ∀ j, x j ^ 2 = if j ∈ S then s else 0 := by
    intro j
    by_cases hj : j ∈ S
    · rw [if_pos hj]
      apply mul_left_cancel₀ (hxS j hj)
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) cubic j
    · rw [if_neg hj, hxnS j hj]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  have hsum2 : ∑ j, x j ^ 2 = (S.card : Kf) * s := by
    rw [Finset.sum_congr rfl (fun j _ => hsq j), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
  rw [Fin.sum_univ_five] at hsum2
  have hcard : S.card ≤ 2 := by
    rcases S.eq_empty_or_nonempty with h0 | ⟨j, hj⟩
    · rw [h0]
      simp
    · have hs0 : s ≠ 0 := by
        have h := hsq j
        rw [if_pos hj] at h
        rw [← h]
        exact pow_ne_zero 2 (hxS j hj)
      have h2 : ((S.card : Kf) - 2) * s = 0 := by
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * hsum2 - 2 * hsdef
      have h5 : (S.card : Kf) = 2 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hs0)
      have h6 : S.card = 2 := cast_two S.card ((Finset.card_le_univ S).trans (by simp)) (sub_eq_zero.mpr h5)
      omega
  rcases S.eq_empty_or_nonempty with h0 | h0
  · have hc0 : S.card = 0 := by
      rw [h0]
      exact Finset.card_empty
    omega
  · have hl := hlt h0
    omega

set_option maxHeartbeats 800000 in
theorem two_line_pattern (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0)
    (z : (M45 Kf)) (hz : z ∈ N) (a b : Fin 5) (hab : indep (col z a) (col z b))
    (hspan : ∀ m, ∃ s t : Kf, col z m = s • col z a + t • col z b) :
    ∃ σ : Equiv.Perm (Fin 5), σ 0 = a ∧ σ 2 = b ∧ col z (σ 1) = (-1 : Kf) • col z a ∧
      col z (σ 3) = (-1 : Kf) • col z b ∧ col z (σ 4) = 0 := by
  have hua1 := C1 N hN z hz a
  have hua2 := Niso N hN hrs z z hz hz a
  have hub1 := C1 N hN z hz b
  have hub2 := Niso N hN hrs z z hz hz b
  choose sc tc hst using hspan
  have hua0 : col z a ≠ 0 := by
    intro h
    have h1 := (hab 1 0 (by rw [h]; simp)).1
    exact one_ne_zero h1
  have hh : ip (col z a) (col z b) ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := Q4 (col z a) (col z b) hua0 hua1 hua2 hub1 hub2 h
    have h1 := (hab c (-1) (by rw [hc]; simp)).2
    norm_num at h1
  have F1 : ∀ m, sc m * tc m = 0 := by
    intro m
    have e := Niso N hN hrs z z hz hz m
    rw [hst m] at e
    have e2 : 2 * (sc m * tc m) * ip (col z a) (col z b) = 0 := by
      simp only [ip, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e hua2 hub2 ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) e - sc m ^ 2 * hua2 - tc m ^ 2 * hub2
    rcases mul_eq_zero.mp e2 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    · exact absurd h hh
  have F2a : sc a = 1 ∧ tc a = 0 := by
    have e := hst a
    have h := hab (sc a - 1) (tc a) (by
      funext i
      have hi := congrFun e i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * hi)
    exact ⟨sub_eq_zero.mp h.1, h.2⟩
  have F2b : sc b = 0 ∧ tc b = 1 := by
    have e := hst b
    have h := hab (sc b) (tc b - 1) (by
      funext i
      have hi := congrFun e i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * hi)
    exact ⟨h.1, sub_eq_zero.mp h.2⟩
  have F3 : (∑ m, sc m) = 0 ∧ (∑ m, tc m) = 0 := by
    apply hab
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e1 : ∑ m, col z m i = 0 := by
      have h := congrFun (sum_cols z) i
      rw [Finset.sum_apply, hrs z hz] at h
      exact h
    have e2 : ∑ m, col z m i = (∑ m, sc m) * col z a i + (∑ m, tc m) * col z b i := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h := congrFun (hst m) i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
    rw [← e2]
    exact e1
  obtain ⟨a', ha'a, hsa'⟩ : ∃ a', a' ≠ a ∧ sc a' ≠ 0 := by
    by_contra hcon
    have hz0 : ∀ m, m ≠ a → sc m = 0 := by
      intro m hm
      by_contra h
      exact hcon ⟨m, hm, h⟩
    have h1 : ∑ m, sc m = sc a :=
      Finset.sum_eq_single a (fun m _ hm => hz0 m hm) (fun h => absurd (Finset.mem_univ a) h)
    rw [F3.1, F2a.1] at h1
    exact zero_ne_one h1
  obtain ⟨b', hb'b, htb'⟩ : ∃ b', b' ≠ b ∧ tc b' ≠ 0 := by
    by_contra hcon
    have hz0 : ∀ m, m ≠ b → tc m = 0 := by
      intro m hm
      by_contra h
      exact hcon ⟨m, hm, h⟩
    have h1 : ∑ m, tc m = tc b :=
      Finset.sum_eq_single b (fun m _ hm => hz0 m hm) (fun h => absurd (Finset.mem_univ b) h)
    rw [F3.2, F2b.2] at h1
    exact zero_ne_one h1
  have hta' : tc a' = 0 := (mul_eq_zero.mp (F1 a')).resolve_left hsa'
  have hsb' : sc b' = 0 := (mul_eq_zero.mp (F1 b')).resolve_right htb'
  have hne_ab : a ≠ b := by
    intro h
    apply one_ne_zero (α := Kf)
    rw [← F2a.1, h, F2b.1]
  have hne_ab' : a ≠ b' := by
    intro h
    apply htb'
    rw [← h, F2a.2]
  have hne_a'b : a' ≠ b := by
    intro h
    apply hsa'
    rw [h, F2b.1]
  have hne_a'b' : a' ≠ b' := by
    intro h
    apply htb'
    rw [← h, hta']
  obtain ⟨σ, h0, h1, h2, h3⟩ := perm_four a a' b b' ha'a.symm hne_ab hne_ab' hne_a'b hne_a'b'
    hb'b.symm
  have hSs : sc a + sc a' + sc b + sc b' + sc (σ 4) = 0 := by
    have h : ∑ j, sc (σ j) = ∑ m, sc m := Equiv.sum_comp σ sc
    rw [Fin.sum_univ_five, F3.1, h0, h1, h2, h3] at h
    exact h
  have hSt : tc a + tc a' + tc b + tc b' + tc (σ 4) = 0 := by
    have h : ∑ j, tc (σ j) = ∑ m, tc m := Equiv.sum_comp σ tc
    rw [Fin.sum_univ_five, F3.2, h0, h1, h2, h3] at h
    exact h
  rw [F2a.1, F2b.1, hsb'] at hSs
  rw [F2a.2, F2b.2, hta'] at hSt
  have za : col z a' = sc a' • col z a := by
    rw [hst a', hta', zero_smul, add_zero]
  have zb : col z b' = tc b' • col z b := by
    rw [hst b', hsb', zero_smul, zero_add]
  by_cases hse : sc (σ 4) = 0
  · by_cases hte : tc (σ 4) = 0
    · have hsa'1 : sc a' = -1 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hSs - hse
      have htb'1 : tc b' = -1 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hSt - hte
      refine ⟨σ, h0, h2, ?_, ?_, ?_⟩
      · rw [h1, za, hsa'1]
      · rw [h3, zb, htb'1]
      · rw [hst (σ 4), hse, hte, zero_smul, zero_smul, add_zero]
    · exfalso
      have hsa'1 : sc a' = -1 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hSs - hse
      have c0 : col z (σ 0) = (1 : Kf) • col z a := by rw [h0, one_smul]
      have c1 : col z (σ 1) = (-1 : Kf) • col z a := by rw [h1, za, hsa'1]
      have c2 : col z (σ 2) = (1 : Kf) • col z b := by rw [h2, one_smul]
      have c3 : col z (σ 3) = tc b' • col z b := by rw [h3, zb]
      have c4 : col z (σ 4) = tc (σ 4) • col z b := by
        rw [hst (σ 4), hse, zero_smul, zero_add]
      exact pattern23 N hN z hz σ (col z a) (col z b) hua1 hua2 hub1 hub2 hab 1 1 (tc b')
        (tc (σ 4)) one_ne_zero one_ne_zero htb' hte c0 c1 c2 c3 c4
  · exfalso
    have hte : tc (σ 4) = 0 := (mul_eq_zero.mp (F1 (σ 4))).resolve_left hse
    have htb'1 : tc b' = -1 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hSt - hte
    have c0 : col z ((σ * swp) 0) =
        (1 : Kf) • col z b := by
      rw [Equiv.Perm.mul_apply, swp0, h2, one_smul]
    have c1 : col z ((σ * swp) 1) =
        (-1 : Kf) • col z b := by
      rw [Equiv.Perm.mul_apply, swp1, h3, zb, htb'1]
    have c2 : col z ((σ * swp) 2) =
        (1 : Kf) • col z a := by
      rw [Equiv.Perm.mul_apply, swp2, h0, one_smul]
    have c3 : col z ((σ * swp) 3) =
        sc a' • col z a := by
      rw [Equiv.Perm.mul_apply, swp3, h1, za]
    have c4 : col z ((σ * swp) 4) =
        sc (σ 4) • col z a := by
      rw [Equiv.Perm.mul_apply, swp4, hst (σ 4), hte, zero_smul, add_zero]
    exact pattern23 N hN z hz (σ * swp) (col z b)
      (col z a) hub1 hub2 hua1 hua2 ((indep_symm (Kf := Kf)) hab) 1 1 (sc a') (sc (σ 4)) one_ne_zero
      one_ne_zero hsa' hse c0 c1 c2 c3 c4

set_option maxHeartbeats 800000 in
theorem typeII_ids (N : Submodule Kf (M45 Kf)) (hN : SLev N) (z : (M45 Kf)) (hz : z ∈ N)
    (σ : Equiv.Perm (Fin 5)) (v w : (V4 Kf)) (c0 : col z (σ 0) = v)
    (c1 : col z (σ 1) = (-1 : Kf) • v) (c2 : col z (σ 2) = w)
    (c3 : col z (σ 3) = (-1 : Kf) • w) (c4 : col z (σ 4) = 0) :
    t3 v w w = 0 ∧ t3 v v w = 0 ∧ br v v w w = 0 := by
  have hNσ := SLev_perm σ N hN
  have hzσ : (cperm (Kf := Kf)) σ z ∈ N.map ((cperm (Kf := Kf)) σ) := Submodule.mem_map_of_mem hz
  have k0 := C34 _ hNσ _ hzσ 0
  have k2 := C34 _ hNσ _ hzσ 2
  have k4 := C34 _ hNσ _ hzσ 4
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at k0
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at k2
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at k4
  have d0 : col ((cperm (Kf := Kf)) σ z) 0 = v := c0
  have d1 : col ((cperm (Kf := Kf)) σ z) 1 = (-1 : Kf) • v := c1
  have d2 : col ((cperm (Kf := Kf)) σ z) 2 = w := c2
  have d3 : col ((cperm (Kf := Kf)) σ z) 3 = (-1 : Kf) • w := c3
  have d4 : col ((cperm (Kf := Kf)) σ z) 4 = 0 := c4
  rw [d1, d2, d3, d4] at k0
  rw [d0, d1, d3, d4] at k2
  rw [d0, d1, d2, d3] at k4
  have a1 := k0.2.1
  have a2 := k2.2.1
  have a3 := k4.2.2
  simp only [t3, br, t4, ip, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a1 a2 a3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a1
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a2
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a3

theorem A1cols [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (v : (V4 Kf)) (hv : v ≠ 0)
    (hv1 : tau v = 0) (hv2 : ip v v = 0)
    (hform : ∀ Z ∈ N, ∃ x : Fin 5 → Kf, Z = outer v x) (h4 : t4 v v v v ≠ 0) :
    ∃ j1 j2 : Fin 5, j1 ≠ j2 ∧ ∀ Z ∈ N, col Z j1 = 0 ∧ col Z j2 = 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 5), ∀ j, j ∈ S ↔ lfN N i0 j ≠ 0 := by
    classical
    exact ⟨Finset.univ.filter (fun j => lfN N i0 j ≠ 0), fun j => by simp⟩
  have hnS : ∀ j, j ∉ S → ∀ Z ∈ N, Z (i0, j) = 0 := by
    intro j hj Z hZ
    have h0 : lfN N i0 j = 0 := by
      by_contra h
      exact hj ((hS j).mpr h)
    exact LinearMap.congr_fun h0 ⟨Z, hZ⟩
  obtain ⟨z, hz⟩ := generic_pt S (lfN N i0) (fun j hj => (hS j).mp hj)
    ((Finset.card_le_univ S).trans (by simp))
  obtain ⟨x, hx⟩ := hform z.1 z.2
  have hZx : outer v x ∈ N := by
    rw [← hx]
    exact z.2
  have hxS : ∀ j, j ∈ S → x j ≠ 0 := by
    intro j hj h0
    apply hz j hj
    rw [lfN_apply, hx]
    simp [outer, h0]
  have hxnS : ∀ j, j ∉ S → x j = 0 := by
    intro j hj
    have h : outer v x (i0, j) = 0 := hnS j hj _ hZx
    simp only [outer] at h
    exact (mul_eq_zero.mp h).resolve_left hi0
  have hker : (N ⊓ LinearMap.ker ((psiS (Kf := Kf)) S i0) : Submodule Kf (M45 Kf)) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz' := Submodule.mem_inf.mp hZ
    obtain ⟨y, hy⟩ := hform Z hz'.1
    have hψ : (psiS (Kf := Kf)) S i0 Z = 0 := LinearMap.mem_ker.mp hz'.2
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h : Z (i0, j) = 0 := by
        by_cases hj : j ∈ S
        · exact congrFun hψ ⟨j, hj⟩
        · exact hnS j hj Z hz'.1
      rw [hy] at h
      simp only [outer] at h
      exact (mul_eq_zero.mp h).resolve_left hi0
    rw [hy]
    funext p
    simp [outer, hy0]
  have r := rank_nullity N ((psiS (Kf := Kf)) S i0)
  rw [hker, finrank_bot] at r
  have hle : Module.finrank Kf (N.map ((psiS (Kf := Kf)) S i0)) ≤ S.card := by
    have h := Submodule.finrank_le (N.map ((psiS (Kf := Kf)) S i0))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
    exact h
  have hsum : ∀ Z ∈ N, ∑ j : ↥S, Z (i0, j.1) = 0 := by
    intro Z hZ
    have h1 : ∑ j : ↥S, Z (i0, j.1) = ∑ j ∈ S, Z (i0, j) :=
      Finset.sum_coe_sort S (fun j => Z (i0, j))
    have h2 : ∑ j ∈ S, Z (i0, j) = ∑ j, Z (i0, j) :=
      Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hnS j hj Z hZ)
    have h3 := congrFun (hrs Z hZ) i0
    rw [rs_apply] at h3
    rw [h1, h2, Fin.sum_univ_five]
    exact h3
  have hlt : S.Nonempty → Module.finrank Kf (N.map ((psiS (Kf := Kf)) S i0)) < S.card := by
    rintro ⟨j0, hj0⟩
    have hsub : N.map ((psiS (Kf := Kf)) S i0) ≤
        LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → Kf) →ₗ[Kf] Kf)) := by
      rintro _ ⟨Z, hZ, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sum_apply]
      exact hsum Z hZ
    have hne' : LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → Kf) →ₗ[Kf] Kf)) ≠ ⊤ := by
      intro h
      have hm : (Pi.single (⟨j0, hj0⟩ : ↥S) (1 : Kf)) ∈
          LinearMap.ker (∑ j : ↥S, (LinearMap.proj j : (↥S → Kf) →ₗ[Kf] Kf)) :=
        h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sum_apply] at hm
      simp at hm
    have h1 := Submodule.finrank_lt hne'
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
    exact lt_of_le_of_lt (Submodule.finrank_mono hsub) h1
  have hprod : ∀ m : Fin 5, ∃ k : Fin 4, m.succAbove k ∉ S := by
    intro m
    have h := (A1facts N hN v hv2 x hZx m).2
    have h' := (mul_eq_zero.mp h).resolve_left h4
    rcases mul_eq_zero.mp h' with h3 | h3
    · rcases mul_eq_zero.mp h3 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h1 | h1
        · exact ⟨0, fun hin => hxS _ hin h1⟩
        · exact ⟨1, fun hin => hxS _ hin h1⟩
      · exact ⟨2, fun hin => hxS _ hin h2⟩
    · exact ⟨3, fun hin => hxS _ hin h3⟩
  obtain ⟨k1, hk1⟩ := hprod 0
  obtain ⟨k2, hk2⟩ := hprod ((0 : Fin 5).succAbove k1)
  refine ⟨(0 : Fin 5).succAbove k1, ((0 : Fin 5).succAbove k1).succAbove k2,
    (Fin.succAbove_ne _ _).symm, fun Z hZ => ?_⟩
  have hc : ∀ j, j ∉ S → col Z j = 0 := by
    intro j hj
    obtain ⟨y, hy⟩ := hform Z hZ
    have h := hnS j hj Z hZ
    rw [hy] at h
    simp only [outer] at h
    have hyj : y j = 0 := (mul_eq_zero.mp h).resolve_left hi0
    rw [hy]
    funext i
    simp [col, outer, hyj]
  exact ⟨hc _ hk1, hc _ hk2⟩

theorem cols_zero (σ : Equiv.Perm (Fin 5)) (Z : (M45 Kf)) (h : ∀ j, col Z (σ j) = 0) : Z = 0 := by
  funext ⟨i, m⟩
  have hh := congrFun (h (σ.symm m)) i
  rw [Equiv.apply_symm_apply] at hh
  exact hh

theorem S6_active (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0)
    (hd : Module.finrank Kf N = 2) (z : (M45 Kf))
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m) (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hind : ∀ s1 s2 s3 : Kf, s1 • col z a + s2 • col z b + s3 • col z c = 0 →
      s1 = 0 ∧ s2 = 0 ∧ s3 = 0) : ∀ m, col z m ≠ 0 := by
  intro m hm
  have hma : a ≠ m := by
    intro h
    have h1 := (hind 1 0 0 (by rw [h, hm]; simp)).1
    exact one_ne_zero h1
  have hmb : b ≠ m := by
    intro h
    have h1 := (hind 0 1 0 (by rw [h, hm]; simp)).2.1
    exact one_ne_zero h1
  have hmc : c ≠ m := by
    intro h
    have h1 := (hind 0 0 1 (by rw [h, hm]; simp)).2.2
    exact one_ne_zero h1
  obtain ⟨σ, h0, h1, h2, h3⟩ := perm_four a b c m hab hac hma hbc hmb hmc
  have p := peel N hN hrs (σ 4)
  have hbot : (N ⊓ LinearMap.ker ((colL (Kf := Kf)) (σ 4)) : Submodule Kf (M45 Kf)) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    have hz1 := Submodule.mem_inf.mp hZ
    have hZN := hz1.1
    have c4 : col Z (σ 4) = 0 := LinearMap.mem_ker.mp hz1.2
    obtain ⟨s1, e1⟩ := hmax Z hZN a
    obtain ⟨s2, e2⟩ := hmax Z hZN b
    obtain ⟨s3, e3⟩ := hmax Z hZN c
    obtain ⟨s4, e4⟩ := hmax Z hZN m
    rw [hm, smul_zero] at e4
    have hsum := sum_cols_perm σ Z
    rw [h0, h1, h2, h3, c4, hrs Z hZN, e1, e2, e3, e4, add_zero, add_zero] at hsum
    obtain ⟨u1, u2, u3⟩ := hind s1 s2 s3 hsum
    apply cols_zero σ
    apply fin5
    · rw [h0, e1, u1, zero_smul]
    · rw [h1, e2, u2, zero_smul]
    · rw [h2, e3, u3, zero_smul]
    · rw [h3]
      exact e4
    · exact c4
  rw [hbot, finrank_bot] at p
  omega

theorem SLev_N (K : Submodule Kf (M45 Kf)) (hK : SLev K) :
    SLev (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) :=
  fun Y hY a => hK Y (Submodule.mem_inf.mp hY).1 a

theorem rs_N (K : Submodule Kf (M45 Kf)) :
    ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), (rs (Kf := Kf)) Z = 0 :=
  fun _ hZ => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hZ).2

set_option maxHeartbeats 800000 in
theorem col_outer (v : (V4 Kf)) (x : Fin 5 → Kf) (m : Fin 5) : col (outer v x) m = x m • v := by
  funext i
  simp only [col, outer, Pi.smul_apply, smul_eq_mul]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

def sw02 : Equiv.Perm (Fin 5) := Equiv.swap 0 2

theorem sw02_0 : sw02 0 = 2 := by decide

theorem sw02_3 : sw02 3 = 3 := by decide

theorem sw02_4 : sw02 4 = 4 := by decide

set_option maxHeartbeats 800000 in
theorem S8_elem (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0)
    (hd : Module.finrank Kf N = 2) (v : (V4 Kf)) (hv : v ≠ 0)
    (hform : ∀ Z ∈ N, ∃ x : Fin 5 → Kf, Z = outer v x) (σ : Equiv.Perm (Fin 5))
    (h3 : ∀ Z ∈ N, col Z (σ 3) = 0) (h4 : ∀ Z ∈ N, col Z (σ 4) = 0) :
    ∃ W ∈ N, col W (σ 0) = v ∧ col W (σ 1) = (-1 : Kf) • v ∧ col W (σ 2) = 0 ∧
      col W (σ 3) = 0 ∧ col W (σ 4) = 0 := by
  have p := peel N hN hrs (σ 2)
  have hne : (N ⊓ LinearMap.ker ((colL (Kf := Kf)) (σ 2)) : Submodule Kf (M45 Kf)) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at p
    omega
  obtain ⟨W0, hW0, hW0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw := Submodule.mem_inf.mp hW0
  have hWN := hw.1
  have a2 : col W0 (σ 2) = 0 := LinearMap.mem_ker.mp hw.2
  have a3 := h3 W0 hWN
  have a4 := h4 W0 hWN
  obtain ⟨x, hx⟩ := hform W0 hWN
  have b0 : col W0 (σ 0) = x (σ 0) • v := by rw [hx, col_outer]
  have b1 : col W0 (σ 1) = x (σ 1) • v := by rw [hx, col_outer]
  have hsum := sum_cols_perm σ W0
  rw [b0, b1, a2, a3, a4, hrs W0 hWN, add_zero, add_zero, add_zero, ← add_smul] at hsum
  have hx01 : x (σ 0) + x (σ 1) = 0 := (smul_eq_zero.mp hsum).resolve_right hv
  have hx1 : x (σ 1) = -x (σ 0) := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hx01
  have hx0 : x (σ 0) ≠ 0 := by
    intro h
    apply hW0ne
    apply cols_zero σ
    apply fin5
    · rw [b0, h, zero_smul]
    · rw [b1, hx1, h, neg_zero, zero_smul]
    · exact a2
    · exact a3
    · exact a4
  refine ⟨(x (σ 0))⁻¹ • W0, N.smul_mem _ hWN, ?_, ?_, ?_, ?_, ?_⟩
  · show (x (σ 0))⁻¹ • col W0 (σ 0) = v
    rw [b0, smul_smul, inv_mul_cancel₀ hx0, one_smul]
  · show (x (σ 0))⁻¹ • col W0 (σ 1) = (-1 : Kf) • v
    rw [b1, hx1, smul_smul, mul_neg, inv_mul_cancel₀ hx0]
  · show (x (σ 0))⁻¹ • col W0 (σ 2) = 0
    rw [a2, smul_zero]
  · show (x (σ 0))⁻¹ • col W0 (σ 3) = 0
    rw [a3, smul_zero]
  · show (x (σ 0))⁻¹ • col W0 (σ 4) = 0
    rw [a4, smul_zero]

set_option maxHeartbeats 800000 in
theorem S8_step1 (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Yu : (M45 Kf)) (hYu : Yu ∈ K)
    (hu : ip ((rs (Kf := Kf)) Yu) ((rs (Kf := Kf)) Yu) = 0)
    (hd : Module.finrank Kf (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) = 2) (v : (V4 Kf))
    (hv : v ≠ 0) (hv3 : t3 v v v = 0)
    (hform : ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), ∃ x : Fin 5 → Kf,
      Z = outer v x)
    (σ : Equiv.Perm (Fin 5))
    (h3 : ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), col Z (σ 3) = 0)
    (h4 : ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), col Z (σ 4) = 0) :
    t3 v v ((rs (Kf := Kf)) Yu) = 0 ∧ t3 v v ((phi (Kf := Kf)) (σ 3) Yu) = 0 ∧ t3 v v ((phi (Kf := Kf)) (σ 4) Yu) = 0 := by
  have hNs := SLev_N K hK
  have hrsN := rs_N K
  obtain ⟨W, hWN, w0, w1, w2, w3, w4⟩ := S8_elem _ hNs hrsN hd v hv hform σ h3 h4
  have hWK : W ∈ K := (Submodule.mem_inf.mp hWN).1
  have hKσ := SLev_perm σ K hK
  have e0 : ∀ i, W (i, σ 0) = v i := fun i => congrFun w0 i
  have e1 : ∀ i, W (i, σ 1) = -1 * v i := fun i => congrFun w1 i
  have e2 : ∀ i, W (i, σ 2) = 0 := fun i => congrFun w2 i
  have e3 : ∀ i, W (i, σ 3) = 0 := fun i => congrFun w3 i
  have e4 : ∀ i, W (i, σ 4) = 0 := fun i => congrFun w4 i
  have A : t3 v v (col Yu (σ 2)) + t3 v v (col Yu (σ 3)) = 0 := by
    have kp := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.add_mem hYu hWK)) 4).2.1
    have km := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.sub_mem hYu hWK)) 4).2.1
    have k0 := (C34 _ hKσ _ (Submodule.mem_map_of_mem hYu) 4).2.1
    rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at kp km k0
    simp only [t3, col, cperm_apply, Pi.add_apply, Pi.sub_apply, e0, e1, e2, e3, e4]
      at kp km k0
    simp only [t3, col]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 2 : Kf) * (kp + km - 2 * k0)
  have B : t3 v v (col Yu (σ 2)) + t3 v v (col Yu (σ 4)) = 0 := by
    have kp := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.add_mem hYu hWK)) 3).2.1
    have km := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.sub_mem hYu hWK)) 3).2.1
    have k0 := (C34 _ hKσ _ (Submodule.mem_map_of_mem hYu) 3).2.1
    rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at kp km k0
    simp only [t3, col, cperm_apply, Pi.add_apply, Pi.sub_apply, e0, e1, e2, e3, e4]
      at kp km k0
    simp only [t3, col]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 2 : Kf) * (kp + km - 2 * k0)
  have C : t3 v v (col Yu (σ 3)) + t3 v v (col Yu (σ 4)) = 0 := by
    have kp := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.add_mem hYu hWK)) 2).2.1
    have km := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.sub_mem hYu hWK)) 2).2.1
    have k0 := (C34 _ hKσ _ (Submodule.mem_map_of_mem hYu) 2).2.1
    rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at kp km k0
    simp only [t3, col, cperm_apply, Pi.add_apply, Pi.sub_apply, e0, e1, e2, e3, e4]
      at kp km k0
    simp only [t3, col]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 2 : Kf) * (kp + km - 2 * k0)
  obtain ⟨W', hW'N, w0', _, _, _, _⟩ := S8_elem _ hNs hrsN hd v hv hform (σ * sw02)
    (fun Z hZ => by
      rw [Equiv.Perm.mul_apply, sw02_3]
      exact h3 Z hZ)
    (fun Z hZ => by
      rw [Equiv.Perm.mul_apply, sw02_4]
      exact h4 Z hZ)
  rw [Equiv.Perm.mul_apply, sw02_0] at w0'
  have hne2 : col W' (σ 2) ≠ 0 := by
    rw [w0']
    exact hv
  obtain ⟨c, hc⟩ := Biii K hK Yu hYu hu W' hW'N (σ 2) hne2
  rw [w0'] at hc
  have f2 : ∀ i, 2 * Yu (i, σ 2) - (rs (Kf := Kf)) Yu i = c * v i := fun i => congrFun hc i
  have f20 := f2 0
  have f21 := f2 1
  have f22 := f2 2
  have f23 := f2 3
  simp only [t3, col] at A B C hv3
  refine ⟨?_, ?_, ?_⟩
  · simp only [t3]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) A + B - C
      - (v 0 * v 0 * f20 + v 1 * v 1 * f21 + v 2 * v 2 * f22 + v 3 * v 3 * f23) - c * hv3
  · simp only [t3, phi_apply]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-2 : Kf) * B + 2 * C
      + (v 0 * v 0 * f20 + v 1 * v 1 * f21 + v 2 * v 2 * f22 + v 3 * v 3 * f23) + c * hv3
  · simp only [t3, phi_apply]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-2 : Kf) * A + 2 * C
      + (v 0 * v 0 * f20 + v 1 * v 1 * f21 + v 2 * v 2 * f22 + v 3 * v 3 * f23) + c * hv3

theorem line_form (N : Submodule Kf (M45 Kf)) (z : (M45 Kf))
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m) (m0 : Fin 5)
    (hline : ∀ m, ∃ c : Kf, col z m = c • col z m0) :
    ∀ Z ∈ N, ∃ x : Fin 5 → Kf, Z = outer (col z m0) x := by
  intro Z hZ
  have h : ∀ m, ∃ d : Kf, col Z m = d • col z m0 := by
    intro m
    obtain ⟨c, hc⟩ := hmax Z hZ m
    obtain ⟨c', hc'⟩ := hline m
    exact ⟨c * c', by rw [hc, hc', smul_smul]⟩
  choose x hx using h
  refine ⟨x, ?_⟩
  funext ⟨i, m⟩
  have hh := congrFun (hx m) i
  simp only [col, Pi.smul_apply, smul_eq_mul] at hh
  simp only [outer, col]
  rw [hh, mul_comm]

set_option maxHeartbeats 800000 in
theorem tricho (N : Submodule Kf (M45 Kf)) (z : (M45 Kf))
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m) :
    (∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ s1 s2 s3 : Kf,
      s1 • col z a + s2 • col z b + s3 • col z c = 0 → s1 = 0 ∧ s2 = 0 ∧ s3 = 0)
    ∨ (∃ a b : Fin 5, indep (col z a) (col z b) ∧
      ∀ m, ∃ s t : Kf, col z m = s • col z a + t • col z b)
    ∨ (∃ m0 : Fin 5, col z m0 ≠ 0 ∧ ∀ Z ∈ N, ∃ x : Fin 5 → Kf, Z = outer (col z m0) x)
    ∨ N = ⊥ := by
  by_cases h2 : ∃ a b : Fin 5, indep (col z a) (col z b)
  · obtain ⟨a, b, hab⟩ := h2
    by_cases h3 : ∃ c : Fin 5, ∀ s1 s2 s3 : Kf,
        s1 • col z a + s2 • col z b + s3 • col z c = 0 → s1 = 0 ∧ s2 = 0 ∧ s3 = 0
    · obtain ⟨c, hc⟩ := h3
      have hne_ab : a ≠ b := by
        intro h
        have h1 := (hab 1 (-1) (by rw [h]; simp)).1
        exact one_ne_zero h1
      have hne_ac : a ≠ c := by
        intro h
        have h1 := (hc 1 0 (-1) (by rw [h]; simp)).1
        exact one_ne_zero h1
      have hne_bc : b ≠ c := by
        intro h
        have h1 := (hc 0 1 (-1) (by rw [h]; simp)).2.1
        exact one_ne_zero h1
      exact Or.inl ⟨a, b, c, hne_ab, hne_ac, hne_bc, hc⟩
    · refine Or.inr (Or.inl ⟨a, b, hab, ?_⟩)
      intro m
      by_contra hcon
      apply h3
      refine ⟨m, fun s1 s2 s3 h => ?_⟩
      have hs3 : s3 = 0 := by
        by_contra hne
        apply hcon
        refine ⟨-s1 * s3⁻¹, -s2 * s3⁻¹, ?_⟩
        funext i
        have hi := congrFun h i
        have hinv := mul_inv_cancel₀ hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) s3⁻¹ * hi - col z m i * hinv
      rw [hs3, zero_smul, add_zero] at h
      obtain ⟨t1, t2⟩ := hab s1 s2 h
      exact ⟨t1, t2, hs3⟩
  · by_cases hall : ∀ m, col z m = 0
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [eq_bot_iff]
      intro Z hZ
      rw [Submodule.mem_bot]
      funext ⟨i, m⟩
      obtain ⟨c, hc⟩ := hmax Z hZ m
      have hh := congrFun hc i
      rw [hall m] at hh
      simpa [col] using hh
    · obtain ⟨m0, hm0⟩ : ∃ m0, col z m0 ≠ 0 := by
        by_contra h
        apply hall
        intro m
        by_contra hm
        exact h ⟨m, hm⟩
      refine Or.inr (Or.inr (Or.inl ⟨m0, hm0, line_form N z hmax m0 ?_⟩))
      intro m
      by_contra hcon
      apply h2
      refine ⟨m0, m, fun s t h => ?_⟩
      have ht : t = 0 := by
        by_contra hne
        apply hcon
        refine ⟨-s * t⁻¹, ?_⟩
        funext i
        have hi := congrFun h i
        have hinv := mul_inv_cancel₀ hne
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) t⁻¹ * hi - col z m i * hinv
      rw [ht, zero_smul, add_zero] at h
      exact ⟨(smul_eq_zero.mp h).resolve_right hm0, ht⟩

def HypS6 : Prop :=
  ∀ N : Submodule Kf (M45 Kf), SLev N → (∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) → Module.finrank Kf N = 2 →
    ∀ z ∈ N, (∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m) →
    ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
    (∀ s1 s2 s3 : Kf, s1 • col z a + s2 • col z b + s3 • col z c = 0 →
      s1 = 0 ∧ s2 = 0 ∧ s3 = 0) → (∀ m, col z m ≠ 0) → False

def HypS7 : Prop :=
  ∀ K : Submodule Kf (M45 Kf), SLev K → Module.finrank Kf (K.map (rs (Kf := Kf))) = 2 →
    (∃ u ∈ K.map (rs (Kf := Kf)), u ≠ 0 ∧ ∀ s ∈ K.map (rs (Kf := Kf)), ip u s = 0) →
    Module.finrank Kf (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) = 2 →
    ∀ z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)),
    (∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), ∀ m, ∃ c : Kf, col Z m = c • col z m) →
    ∀ σ : Equiv.Perm (Fin 5), indep (col z (σ 0)) (col z (σ 2)) →
    col z (σ 1) = (-1 : Kf) • col z (σ 0) → col z (σ 3) = (-1 : Kf) • col z (σ 2) →
    col z (σ 4) = 0 →
    t3 (col z (σ 0)) (col z (σ 2)) (col z (σ 2)) = 0 →
    t3 (col z (σ 0)) (col z (σ 0)) (col z (σ 2)) = 0 →
    br (col z (σ 0)) (col z (σ 0)) (col z (σ 2)) (col z (σ 2)) = 0 → False

def HypS8 : Prop :=
  ∀ K : Submodule Kf (M45 Kf), SLev K → Module.finrank Kf (K.map (rs (Kf := Kf))) = 2 →
    Module.finrank Kf (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) = 2 →
    ∀ Yu ∈ K, (rs (Kf := Kf)) Yu ≠ 0 → (∀ s ∈ K.map (rs (Kf := Kf)), ip ((rs (Kf := Kf)) Yu) s = 0) →
    ∀ v : (V4 Kf), v ≠ 0 → tau v = 0 → ip v v = 0 → t3 v v v = 0 →
    (∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), ∃ x : Fin 5 → Kf, Z = outer v x) →
    ∀ σ : Equiv.Perm (Fin 5),
    (∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), col Z (σ 3) = 0) →
    (∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), col Z (σ 4) = 0) →
    t3 v v ((rs (Kf := Kf)) Yu) = 0 → t3 v v ((phi (Kf := Kf)) (σ 3) Yu) = 0 → t3 v v ((phi (Kf := Kf)) (σ 4) Yu) = 0 → False

theorem No22 [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] (H6 : (HypS6 (Kf := Kf))) (H7 : (HypS7 (Kf := Kf))) (H8 : (HypS8 (Kf := Kf))) (K : Submodule Kf (M45 Kf)) (hK : SLev K)
    (hq : Module.finrank Kf (K.map (rs (Kf := Kf))) = 2)
    (hd : Module.finrank Kf (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) = 2) : False := by
  have hNs := SLev_N K hK
  have hrs := rs_N K
  have hne : (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hd
    omega
  have hu := Bii K hK hq hne
  obtain ⟨z, hz, hmax⟩ := maxpt _ hNs hrs
  rcases tricho _ z hmax with ⟨a, b, c, hab, hac, hbc, hind⟩ | ⟨a, b, hab, hspan⟩ |
    ⟨m0, hm0, hform⟩ | hbot
  · exact H6 _ hNs hrs hd z hz hmax a b c hab hac hbc hind
      (S6_active _ hNs hrs hd z hmax a b c hab hac hbc hind)
  · obtain ⟨σ, h0, h2, e1, e3, e4⟩ := two_line_pattern _ hNs hrs z hz a b hab hspan
    subst h0
    subst h2
    have ids := typeII_ids _ hNs z hz σ (col z (σ 0)) (col z (σ 2)) rfl e1 rfl e3 e4
    exact H7 K hK hq hu hd z hz hmax σ hab e1 e3 e4 ids.1 ids.2.1 ids.2.2
  · by_cases h3 : t3 (col z m0) (col z m0) (col z m0) = 0
    · have h4 : t4 (col z m0) (col z m0) (col z m0) (col z m0) ≠ 0 := fun h =>
        hm0 (iso34 _ (C1 _ hNs z hz m0) (Niso _ hNs hrs z z hz hz m0) h3 h)
      obtain ⟨j1, j2, hj, hcols⟩ := A1cols _ hNs hrs (col z m0) hm0 (C1 _ hNs z hz m0)
        (Niso _ hNs hrs z z hz hz m0) hform h4
      obtain ⟨σ, s3, s4⟩ := perm_two (3 : Fin 5) 4 j1 j2 (by decide) hj
      obtain ⟨u, huS, hu0, huperp⟩ := hu
      obtain ⟨Yu, hYu, rfl⟩ := huS
      have huu : ip ((rs (Kf := Kf)) Yu) ((rs (Kf := Kf)) Yu) = 0 := huperp _ (Submodule.mem_map_of_mem hYu)
      have c3 : ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), col Z (σ 3) = 0 :=
        fun Z hZ => by
          rw [s3]
          exact (hcols Z hZ).1
      have c4 : ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), col Z (σ 4) = 0 :=
        fun Z hZ => by
          rw [s4]
          exact (hcols Z hZ).2
      have st := S8_step1 K hK Yu hYu huu hd (col z m0) hm0 h3 hform σ c3 c4
      exact H8 K hK hq hd Yu hYu hu0 huperp (col z m0) hm0 (C1 _ hNs z hz m0)
        (Niso _ hNs hrs z z hz hz m0) h3 hform σ c3 c4 st.1 st.2.1 st.2.2
    · have h1 := A1b _ hNs hrs (col z m0) hm0 (C1 _ hNs z hz m0)
        (Niso _ hNs hrs z z hz hz m0) hform h3
      omega
  · exact hne hbot

theorem SL_of [Fact (∀ s : Finset Kf, s.card ≤ 20 → ∃ t : Kf, t ∉ s)] (H6 : (HypS6 (Kf := Kf))) (H7 : (HypS7 (Kf := Kf))) (H8 : (HypS8 (Kf := Kf)))
    (K : Submodule Kf (M45 Kf)) (hK : SLev K) : Module.finrank Kf K ≤ 3 := by
  have r := rank_nullity K (rs (Kf := Kf))
  have hq := (Submodule.finrank_mono (map_rs_le K hK)).trans (finrank_sumZero (Kf := Kf) (n := 4) (by norm_num))
  have hd := LemA_proof _ (SLev_N K hK) (rs_N K)
  by_cases h3 : Module.finrank Kf (K.map (rs (Kf := Kf))) = 3
  · have hb := Bi K hK h3
    rw [hb, finrank_bot] at r
    omega
  · by_cases h2 : Module.finrank Kf (K.map (rs (Kf := Kf))) = 2 ∧
        Module.finrank Kf (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) = 2
    · exact (No22 H6 H7 H8 K hK h2.1 h2.2).elim
    · omega


def r3 [Fact (∃ i : Kf, i ^ 2 = -1)] : Fin 3 → Kf := ![((Ii (Kf := Kf)) : Kf), -1, -((Ii (Kf := Kf)) : Kf)]

def e2 (d : (V4 Kf)) : Kf := (tau d ^ 2 - ip d d) / 2

end

end PEqualNP.Outside.L_gct_210_aux.FLK

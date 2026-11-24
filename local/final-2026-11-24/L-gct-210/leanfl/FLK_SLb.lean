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

set_option maxHeartbeats 800000 in
theorem Niso (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (Z Z' : (M45 Kf))
    (hZ : Z ∈ N) (hZ' : Z' ∈ N) (m : Fin 5) : ip (col Z m) (col Z' m) = 0 := by
  have e := C2pol N hN Z Z' hZ hZ' m
  rw [hrs Z hZ, hrs Z' hZ'] at e
  simp only [ip, Pi.zero_apply] at e ⊢
  linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * e

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

def cperm (σ : Equiv.Perm (Fin 5)) : (M45 Kf) →ₗ[Kf] (M45 Kf) :=
  LinearMap.funLeft Kf Kf (fun p : Fin 4 × Fin 5 => (p.1, σ p.2))

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

def HypS6 : Prop :=
  ∀ N : Submodule Kf (M45 Kf), SLev N → (∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) → Module.finrank Kf N = 2 →
    ∀ z ∈ N, (∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m) →
    ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
    (∀ s1 s2 s3 : Kf, s1 • col z a + s2 • col z b + s3 • col z c = 0 →
      s1 = 0 ∧ s2 = 0 ∧ s3 = 0) → (∀ m, col z m ≠ 0) → False

theorem t3_ip_l (x y z : (V4 Kf)) : t3 x y z = ip (fun i => x i * y i : (V4 Kf)) z := by
  simp only [t3, ip]

def Qv (v : (V4 Kf)) (a0 a1 a2 a3 : Kf) : (V4 Kf) := fun i => a0 + a1 * v i + a2 * v i ^ 2 + a3 * v i ^ 3

set_option maxHeartbeats 800000 in
theorem Qv_mul (v : (V4 Kf)) (kap : Kf) (hk : ∀ i, v i ^ 4 = kap) (a0 a1 a2 a3 b0 b1 b2 b3 : Kf) :
    (fun i => Qv v a0 a1 a2 a3 i * Qv v b0 b1 b2 b3 i : (V4 Kf)) =
      Qv v (a0 * b0 + kap * (a1 * b3 + a2 * b2 + a3 * b1))
        (a0 * b1 + a1 * b0 + kap * (a2 * b3 + a3 * b2))
        (a0 * b2 + a1 * b1 + a2 * b0 + kap * (a3 * b3)) (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  funext i
  simp only [Qv]
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) ((a1 * b3 + a2 * b2 + a3 * b1) + (a2 * b3 + a3 * b2) * v i
    + a3 * b3 * v i ^ 2) * hk i

set_option maxHeartbeats 800000 in
theorem tau_Qv (v : (V4 Kf)) (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0)
    (a0 a1 a2 a3 : Kf) : tau (Qv v a0 a1 a2 a3) = 4 * a0 := by
  simp only [tau, ip, t3] at h1 h2 h3
  simp only [tau, Qv]
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a1 * h1 + a2 * h2 + a3 * h3

theorem ip_Qv (v : (V4 Kf)) (kap : Kf) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a0 a1 a2 a3 b0 b1 b2 b3 : Kf) :
    ip (Qv v a0 a1 a2 a3) (Qv v b0 b1 b2 b3) =
      4 * (a0 * b0 + kap * (a1 * b3 + a2 * b2 + a3 * b1)) := by
  have e : ip (Qv v a0 a1 a2 a3) (Qv v b0 b1 b2 b3) =
      tau (fun i => Qv v a0 a1 a2 a3 i * Qv v b0 b1 b2 b3 i : (V4 Kf)) := by
    simp only [ip, tau]
  rw [e, Qv_mul v kap hk, tau_Qv v h1 h2 h3]

set_option maxHeartbeats 800000 in
def Lv (v : (V4 Kf)) : (V4 Kf) →ₗ[Kf] (V4 Kf) where
  toFun a := Qv v (a 0) (a 1) (a 2) (a 3)
  map_add' a b := by
    funext i
    simp only [Qv, Pi.add_apply]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  map_smul' c a := by
    funext i
    simp only [Qv, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

theorem Lv_apply (v a : (V4 Kf)) : Lv v a = Qv v (a 0) (a 1) (a 2) (a 3) := rfl

set_option maxHeartbeats 800000 in
theorem Qv_inj (v : (V4 Kf)) (kap : Kf) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0)
    (h2 : ip v v = 0) (h3 : t3 v v v = 0) (a0 a1 a2 a3 b0 b1 b2 b3 : Kf)
    (h : Qv v a0 a1 a2 a3 = Qv v b0 b1 b2 b3) : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have e0 : ip (Qv v a0 a1 a2 a3) (Qv v 1 0 0 0) = ip (Qv v b0 b1 b2 b3) (Qv v 1 0 0 0) := by
    rw [h]
  have e1 : ip (Qv v a0 a1 a2 a3) (Qv v 0 0 0 1) = ip (Qv v b0 b1 b2 b3) (Qv v 0 0 0 1) := by
    rw [h]
  have e2 : ip (Qv v a0 a1 a2 a3) (Qv v 0 0 1 0) = ip (Qv v b0 b1 b2 b3) (Qv v 0 0 1 0) := by
    rw [h]
  have e3 : ip (Qv v a0 a1 a2 a3) (Qv v 0 1 0 0) = ip (Qv v b0 b1 b2 b3) (Qv v 0 1 0 0) := by
    rw [h]
  rw [ip_Qv v kap hk h1 h2 h3, ip_Qv v kap hk h1 h2 h3] at e0 e1 e2 e3
  refine ⟨by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * e0, ?_, ?_, ?_⟩
  · apply mul_left_cancel₀ hkap
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * e1
  · apply mul_left_cancel₀ hkap
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * e2
  · apply mul_left_cancel₀ hkap
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * e3

theorem Qv_exists (v : (V4 Kf)) (kap : Kf) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0) (x : (V4 Kf)) :
    ∃ a0 a1 a2 a3 : Kf, x = Qv v a0 a1 a2 a3 := by
  have hinj : Function.Injective (Lv v) := by
    intro a b hab
    rw [Lv_apply, Lv_apply] at hab
    obtain ⟨q0, q1, q2, q3⟩ := Qv_inj v kap hkap hk h1 h2 h3 _ _ _ _ _ _ _ _ hab
    funext i
    fin_cases i
    · exact q0
    · exact q1
    · exact q2
    · exact q3
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective.mp hinj) x
  exact ⟨a 0, a 1, a 2, a 3, ha.symm⟩

set_option maxHeartbeats 800000 in
theorem Qv_V (v : (V4 Kf)) (kap : Kf) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0) (x : (V4 Kf)) (hx : tau x = 0) :
    ∃ p q r : Kf, x = Qv v 0 p q r := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := Qv_exists v kap hkap hk h1 h2 h3 x
  rw [tau_Qv v h1 h2 h3] at hx
  have h0 : a0 = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hx
  subst h0
  exact ⟨a1, a2, a3, rfl⟩


def r3 [Fact (∃ i : Kf, i ^ 2 = -1)] : Fin 3 → Kf := ![((Ii (Kf := Kf)) : Kf), -1, -((Ii (Kf := Kf)) : Kf)]

def spv [Fact (∃ i : Kf, i ^ 2 = -1)] (π : Equiv.Perm (Fin 3)) : (V4 Kf) := ![1, (r3 (Kf := Kf)) (π 0), (r3 (Kf := Kf)) (π 1), (r3 (Kf := Kf)) (π 2)]

set_option maxHeartbeats 800000 in
theorem r3_pow [Fact (∃ i : Kf, i ^ 2 = -1)] (k : Fin 3) : (r3 (Kf := Kf)) k ^ 4 = 1 := by
  fin_cases k
  · show ((Ii (Kf := Kf)) : Kf) ^ 4 = 1
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (((Ii (Kf := Kf)) : Kf) * ((Ii (Kf := Kf)) : Kf) - 1) * (Ii_mul_Ii (Kf := Kf))
  · show (-1 : Kf) ^ 4 = 1
    norm_num
  · show (-((Ii (Kf := Kf)) : Kf)) ^ 4 = 1
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (((Ii (Kf := Kf)) : Kf) * ((Ii (Kf := Kf)) : Kf) - 1) * (Ii_mul_Ii (Kf := Kf))

theorem r3_inj [Fact (∃ i : Kf, i ^ 2 = -1)] : Function.Injective (r3 (Kf := Kf)) := by
  have h1 : ((Ii (Kf := Kf)) : Kf) ≠ -1 := by
    intro h
    apply (nz2 (Kf := Kf))
    linear_combination (Ii_mul_Ii (Kf := Kf)) - (((Ii (Kf := Kf)) : Kf) - 1) * h
  have h2 : ((Ii (Kf := Kf)) : Kf) ≠ -((Ii (Kf := Kf)) : Kf) := by
    intro h
    apply (nz2 (Kf := Kf))
    linear_combination 2 * (Ii_mul_Ii (Kf := Kf)) - ((Ii (Kf := Kf)) : Kf) * h
  have h3 : (-1 : Kf) ≠ -((Ii (Kf := Kf)) : Kf) := by
    intro h
    apply (nz2 (Kf := Kf))
    linear_combination (Ii_mul_Ii (Kf := Kf)) - (((Ii (Kf := Kf)) : Kf) + 1) * h
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h.symm h1
  · rfl
  · exact absurd h h3
  · exact absurd h.symm h2
  · exact absurd h.symm h3
  · rfl

set_option maxHeartbeats 800000 in
theorem r3_sums [Fact (∃ i : Kf, i ^ 2 = -1)] (π : Equiv.Perm (Fin 3)) :
    (r3 (Kf := Kf)) (π 0) + (r3 (Kf := Kf)) (π 1) + (r3 (Kf := Kf)) (π 2) = -1 ∧
    (r3 (Kf := Kf)) (π 0) * (r3 (Kf := Kf)) (π 0) + (r3 (Kf := Kf)) (π 1) * (r3 (Kf := Kf)) (π 1) + (r3 (Kf := Kf)) (π 2) * (r3 (Kf := Kf)) (π 2) = -1 ∧
    (r3 (Kf := Kf)) (π 0) * (r3 (Kf := Kf)) (π 0) * (r3 (Kf := Kf)) (π 0) + (r3 (Kf := Kf)) (π 1) * (r3 (Kf := Kf)) (π 1) * (r3 (Kf := Kf)) (π 1)
      + (r3 (Kf := Kf)) (π 2) * (r3 (Kf := Kf)) (π 2) * (r3 (Kf := Kf)) (π 2) = -1 := by
  have h1 : (r3 (Kf := Kf)) (π 0) + (r3 (Kf := Kf)) (π 1) + (r3 (Kf := Kf)) (π 2) = (r3 (Kf := Kf)) 0 + (r3 (Kf := Kf)) 1 + (r3 (Kf := Kf)) 2 := by
    have h := Equiv.sum_comp π (r3 (Kf := Kf))
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
    exact h
  have h2 : (r3 (Kf := Kf)) (π 0) * (r3 (Kf := Kf)) (π 0) + (r3 (Kf := Kf)) (π 1) * (r3 (Kf := Kf)) (π 1) + (r3 (Kf := Kf)) (π 2) * (r3 (Kf := Kf)) (π 2) =
      (r3 (Kf := Kf)) 0 * (r3 (Kf := Kf)) 0 + (r3 (Kf := Kf)) 1 * (r3 (Kf := Kf)) 1 + (r3 (Kf := Kf)) 2 * (r3 (Kf := Kf)) 2 := by
    have h := Equiv.sum_comp π (fun k => (r3 (Kf := Kf)) k * (r3 (Kf := Kf)) k)
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
    exact h
  have h3 : (r3 (Kf := Kf)) (π 0) * (r3 (Kf := Kf)) (π 0) * (r3 (Kf := Kf)) (π 0) + (r3 (Kf := Kf)) (π 1) * (r3 (Kf := Kf)) (π 1) * (r3 (Kf := Kf)) (π 1)
      + (r3 (Kf := Kf)) (π 2) * (r3 (Kf := Kf)) (π 2) * (r3 (Kf := Kf)) (π 2) =
      (r3 (Kf := Kf)) 0 * (r3 (Kf := Kf)) 0 * (r3 (Kf := Kf)) 0 + (r3 (Kf := Kf)) 1 * (r3 (Kf := Kf)) 1 * (r3 (Kf := Kf)) 1 + (r3 (Kf := Kf)) 2 * (r3 (Kf := Kf)) 2 * (r3 (Kf := Kf)) 2 := by
    have h := Equiv.sum_comp π (fun k => (r3 (Kf := Kf)) k * (r3 (Kf := Kf)) k * (r3 (Kf := Kf)) k)
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
    exact h
  have e0 : (r3 (Kf := Kf)) 0 = ((Ii (Kf := Kf)) : Kf) := rfl
  have e1 : (r3 (Kf := Kf)) 1 = -1 := rfl
  have e2 : (r3 (Kf := Kf)) 2 = -((Ii (Kf := Kf)) : Kf) := rfl
  rw [e0, e1, e2] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h1
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h2 + 2 * (Ii_mul_Ii (Kf := Kf))
  · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h3

set_option maxHeartbeats 800000 in
theorem spv_props [Fact (∃ i : Kf, i ^ 2 = -1)] (π : Equiv.Perm (Fin 3)) :
    tau ((spv (Kf := Kf)) π) = 0 ∧ ip ((spv (Kf := Kf)) π) ((spv (Kf := Kf)) π) = 0 ∧ t3 ((spv (Kf := Kf)) π) ((spv (Kf := Kf)) π) ((spv (Kf := Kf)) π) = 0 ∧
      ∀ i, (spv (Kf := Kf)) π i ^ 4 = 1 := by
  obtain ⟨h1, h2, h3⟩ := (r3_sums (Kf := Kf)) π
  have e0 : (spv (Kf := Kf)) π 0 = 1 := rfl
  have e1 : (spv (Kf := Kf)) π 1 = (r3 (Kf := Kf)) (π 0) := rfl
  have e2 : (spv (Kf := Kf)) π 2 = (r3 (Kf := Kf)) (π 1) := rfl
  have e3 : (spv (Kf := Kf)) π 3 = (r3 (Kf := Kf)) (π 2) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [tau, e0, e1, e2, e3]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h1
  · simp only [ip, e0, e1, e2, e3]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h2
  · simp only [t3, e0, e1, e2, e3]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h3
  · intro i
    fin_cases i
    · show (1 : Kf) ^ 4 = 1
      norm_num
    · exact (r3_pow (Kf := Kf)) (π 0)
    · exact (r3_pow (Kf := Kf)) (π 1)
    · exact (r3_pow (Kf := Kf)) (π 2)

theorem spv_inj [Fact (∃ i : Kf, i ^ 2 = -1)] (π π' : Equiv.Perm (Fin 3)) (h0 : (r3 (Kf := Kf)) (π 0) = (r3 (Kf := Kf)) (π' 0))
    (h1 : (r3 (Kf := Kf)) (π 1) = (r3 (Kf := Kf)) (π' 1)) (h2 : (r3 (Kf := Kf)) (π 2) = (r3 (Kf := Kf)) (π' 2)) : π = π' := by
  apply Equiv.ext
  intro k
  fin_cases k
  · exact (r3_inj (Kf := Kf)) h0
  · exact (r3_inj (Kf := Kf)) h1
  · exact (r3_inj (Kf := Kf)) h2

set_option maxHeartbeats 800000 in
theorem chart [Fact (∃ i : Kf, i ^ 2 = -1)] (c : Fin 5 → (V4 Kf)) (hc : ∀ m, c m ≠ 0) :
    ∃ v : (V4 Kf), tau v = 0 ∧ ip v v = 0 ∧ t3 v v v = 0 ∧ (∀ i, v i ^ 4 = 1) ∧
      ∀ m, ∀ k : Kf, c m ≠ k • v := by
  by_contra hcon
  have hall : ∀ π : Equiv.Perm (Fin 3), ∃ m, ∃ k : Kf, c m = k • (spv (Kf := Kf)) π := by
    intro π
    by_contra h
    apply hcon
    obtain ⟨p1, p2, p3, p4⟩ := (spv_props (Kf := Kf)) π
    exact ⟨(spv (Kf := Kf)) π, p1, p2, p3, p4, fun m k hk => h ⟨m, k, hk⟩⟩
  choose f g hg using hall
  obtain ⟨π, π', hne, hff⟩ := Fintype.exists_ne_map_eq_of_card_lt f
    (by rw [Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]; decide)
  have e := hg π
  rw [hff, hg π'] at e
  have q0 := congrFun e 0
  have q1 := congrFun e 1
  have q2 := congrFun e 2
  have q3 := congrFun e 3
  simp only [Pi.smul_apply, smul_eq_mul] at q0 q1 q2 q3
  have a0 : ∀ ρ : Equiv.Perm (Fin 3), (spv (Kf := Kf)) ρ 0 = 1 := fun ρ => rfl
  have a1 : ∀ ρ : Equiv.Perm (Fin 3), (spv (Kf := Kf)) ρ 1 = (r3 (Kf := Kf)) (ρ 0) := fun ρ => rfl
  have a2 : ∀ ρ : Equiv.Perm (Fin 3), (spv (Kf := Kf)) ρ 2 = (r3 (Kf := Kf)) (ρ 1) := fun ρ => rfl
  have a3 : ∀ ρ : Equiv.Perm (Fin 3), (spv (Kf := Kf)) ρ 3 = (r3 (Kf := Kf)) (ρ 2) := fun ρ => rfl
  rw [a0, a0] at q0
  rw [a1, a1] at q1
  rw [a2, a2] at q2
  rw [a3, a3] at q3
  have hgg : g π' = g π := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) q0
  have hg0 : g π ≠ 0 := by
    intro h0
    apply hc (f π)
    rw [hg π, h0, zero_smul]
  apply hne
  apply (spv_inj (Kf := Kf))
  · apply mul_left_cancel₀ hg0
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -q1 + (r3 (Kf := Kf)) (π' 0) * hgg
  · apply mul_left_cancel₀ hg0
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -q2 + (r3 (Kf := Kf)) (π' 1) * hgg
  · apply mul_left_cancel₀ hg0
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) -q3 + (r3 (Kf := Kf)) (π' 2) * hgg

def Uv (v : (V4 Kf)) (θ : Kf) : (V4 Kf) := Qv v 0 (-(θ ^ 2) / 2) θ 1

def tt (a b c : Kf) : Kf := 4 * (a + b + c) + a * b * c * (a * b + b * c + c * a)

def kk (x y : Kf) : Kf := 2 * x + 4 * y + x ^ 2 * y ^ 3 + x * y ^ 4 / 2

def cc (x : Kf) : Kf := 12 * x + 3 * x ^ 5

set_option maxHeartbeats 800000 in
theorem iso_coords (v : (V4 Kf)) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (x : (V4 Kf)) (hx : tau x = 0) (hxx : ip x x = 0)
    (hnp : ∀ k : Kf, x ≠ k • v) : ∃ θ ζ : Kf, ζ ≠ 0 ∧ x = ζ • Uv v θ := by
  obtain ⟨p, q, r, rfl⟩ := Qv_V v 1 one_ne_zero hk h1 h2 h3 x hx
  rw [ip_Qv v 1 hk h1 h2 h3] at hxx
  have hr : r ≠ 0 := by
    intro hr
    rw [hr] at hxx
    have hq : q = 0 := by
      have hqq : q * q = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hxx
      exact mul_self_eq_zero.mp hqq
    apply hnp p
    funext i
    simp only [Qv, Pi.smul_apply, smul_eq_mul, hr, hq]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  obtain ⟨θ, hθ⟩ : ∃ θ : Kf, q = θ * r := ⟨q / r, (div_mul_cancel₀ q hr).symm⟩
  have hp : 2 * p + θ ^ 2 * r = 0 := by
    apply mul_left_cancel₀ hr
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hxx - (q + θ * r) * hθ
  refine ⟨θ, r, hr, ?_⟩
  funext i
  simp only [Qv, Uv, Pi.smul_apply, smul_eq_mul]
  linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (v i / 2) * hp + (v i ^ 2) * hθ

set_option maxHeartbeats 800000 in
theorem ip_Uv (v : (V4 Kf)) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (θ : Kf) : ip (Uv v θ) v = 4 := by
  have hv' : v = Qv v 0 1 0 0 := by
    funext i
    simp only [Qv]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  have e : ip (Qv v 0 (-(θ ^ 2) / 2) θ 1) (Qv v 0 1 0 0) = 4 := by
    rw [ip_Qv v 1 hk h1 h2 h3]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  rw [← hv'] at e
  exact e

set_option maxHeartbeats 800000 in
theorem t3_smul3 (a b c : Kf) (x y z : (V4 Kf)) : t3 (a • x) (b • y) (c • z) = a * b * c * t3 x y z := by
  simp only [t3, Pi.smul_apply, smul_eq_mul]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem t3_Uv (v : (V4 Kf)) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (a b c : Kf) : t3 (Uv v a) (Uv v b) (Uv v c) = tt a b c := by
  simp only [Uv, tt]
  rw [t3_ip_l, Qv_mul v 1 hk, ip_Qv v 1 hk h1 h2 h3]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
def lamL (v : (V4 Kf)) : (M45 Kf) →ₗ[Kf] (Fin 5 → Kf) where
  toFun Z := fun m => ip (col Z m) v / 4
  map_add' Z Z' := by
    funext m
    simp only [ip, col, Pi.add_apply]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  map_smul' c Z := by
    funext m
    simp only [ip, col, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

theorem lamL_apply (v : (V4 Kf)) (Z : (M45 Kf)) (m : Fin 5) : lamL v Z m = ip (col Z m) v / 4 := rfl

set_option maxHeartbeats 800000 in
theorem N_coords (N : Submodule Kf (M45 Kf)) (z : (M45 Kf))
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m)
    (v : (V4 Kf)) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0)
    (θ ζ : Fin 5 → Kf) (hz : ∀ m, col z m = ζ m • Uv v (θ m)) (Z : (M45 Kf)) (hZ : Z ∈ N)
    (m : Fin 5) : col Z m = lamL v Z m • Uv v (θ m) := by
  obtain ⟨c, hc⟩ := hmax Z hZ m
  have e : lamL v Z m = c * ζ m := by
    rw [lamL_apply, hc, hz m]
    have h4 := ip_Uv v hk h1 h2 h3 (θ m)
    simp only [ip, Pi.smul_apply, smul_eq_mul] at h4 ⊢
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (c * ζ m / 4) * h4
  rw [e, hc, hz m, smul_smul]

def Chart (N : Submodule Kf (M45 Kf)) (v : (V4 Kf)) (θ : Fin 5 → Kf) : Prop :=
  (∀ i, v i ^ 4 = 1) ∧ tau v = 0 ∧ ip v v = 0 ∧ t3 v v v = 0 ∧
    ∀ Z ∈ N, ∀ m, col Z m = lamL v Z m • Uv v (θ m)

set_option maxHeartbeats 800000 in
theorem Uv_sum (v : (V4 Kf)) (hk : ∀ i, v i ^ 4 = 1) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (L0 L1 L2 L3 L4 T0 T1 T2 T3 T4 : Kf)
    (e : L0 • Uv v T0 + L1 • Uv v T1 + L2 • Uv v T2 + L3 • Uv v T3 + L4 • Uv v T4 = 0) :
    (L0 + L1 + L2 + L3 + L4 = 0) ∧ (L0 * T0 + L1 * T1 + L2 * T2 + L3 * T3 + L4 * T4 = 0) ∧
      (L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2 = 0) := by
  have e' : Qv v 0 (-(L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2) / 2)
      (L0 * T0 + L1 * T1 + L2 * T2 + L3 * T3 + L4 * T4) (L0 + L1 + L2 + L3 + L4) =
      Qv v 0 0 0 0 := by
    funext i
    have ei := congrFun e i
    simp only [Uv, Qv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ei ⊢
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) ei
  obtain ⟨_, q1, q2, q3⟩ := Qv_inj v 1 one_ne_zero hk h1 h2 h3 _ _ _ _ _ _ _ _ e'
  exact ⟨q3, q2, by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-2 : Kf) * q1⟩

theorem Lam_rel (N : Submodule Kf (M45 Kf)) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (v : (V4 Kf)) (θ : Fin 5 → Kf)
    (hC : Chart N v θ) (Z : (M45 Kf)) (hZ : Z ∈ N) :
    (∑ n, lamL v Z n = 0) ∧ (∑ n, lamL v Z n * θ n = 0) ∧
      (∑ n, lamL v Z n * θ n ^ 2 = 0) := by
  obtain ⟨hk, h1, h2, h3, hcol⟩ := hC
  have e : col Z 0 + col Z 1 + col Z 2 + col Z 3 + col Z 4 = (rs (Kf := Kf)) Z :=
    sum_cols_perm (Equiv.refl (Fin 5)) Z
  rw [hrs Z hZ, hcol Z hZ 0, hcol Z hZ 1, hcol Z hZ 2, hcol Z hZ 3, hcol Z hZ 4] at e
  rw [Fin.sum_univ_five, Fin.sum_univ_five, Fin.sum_univ_five]
  exact Uv_sum v hk h1 h2 h3 _ _ _ _ _ _ _ _ _ _ e

set_option maxHeartbeats 800000 in
theorem star_cert (L0 L1 L2 L3 L4 T0 T1 T2 T3 T4 : Kf)
    (r0 : L0 + L1 + L2 + L3 + L4 = 0)
    (r1 : L0 * T0 + L1 * T1 + L2 * T2 + L3 * T3 + L4 * T4 = 0)
    (r2 : L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2 = 0)
    (c0 : L1 * L2 * L3 * tt T1 T2 T3 + L1 * L2 * L4 * tt T1 T2 T4 + L1 * L3 * L4 * tt T1 T3 T4
      + L2 * L3 * L4 * tt T2 T3 T4 = 0)
    (c1 : L0 * L2 * L3 * tt T0 T2 T3 + L0 * L2 * L4 * tt T0 T2 T4 + L0 * L3 * L4 * tt T0 T3 T4
      + L2 * L3 * L4 * tt T2 T3 T4 = 0)
    (c2 : L0 * L1 * L3 * tt T0 T1 T3 + L0 * L1 * L4 * tt T0 T1 T4 + L0 * L3 * L4 * tt T0 T3 T4
      + L1 * L3 * L4 * tt T1 T3 T4 = 0)
    (c3 : L0 * L1 * L2 * tt T0 T1 T2 + L0 * L1 * L4 * tt T0 T1 T4 + L0 * L2 * L4 * tt T0 T2 T4
      + L1 * L2 * L4 * tt T1 T2 T4 = 0)
    (c4 : L0 * L1 * L2 * tt T0 T1 T2 + L0 * L1 * L3 * tt T0 T1 T3 + L0 * L2 * L3 * tt T0 T2 T3
      + L1 * L2 * L3 * tt T1 T2 T3 = 0) :
    L0 * (cc T0 * L0 ^ 2 - (L0 ^ 2 * kk T0 T0 + L1 ^ 2 * kk T0 T1 + L2 ^ 2 * kk T0 T2
      + L3 ^ 2 * kk T0 T3 + L4 ^ 2 * kk T0 T4)) = 0 := by
  simp only [tt] at c0 c1 c2 c3 c4
  simp only [cc, kk]
  linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (c0 + c1 + c2 + c3 + c4) - c0
    - L0 * ((2 * T0 * (L0 + L1 + L2 + L3 + L4)
        + 4 * (L0 * T0 + L1 * T1 + L2 * T2 + L3 * T3 + L4 * T4) - 8 * L0 * T0) * r0
      + (T0 ^ 2 * (L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2)
        - L0 * T0 ^ 4 - 4 * L0) * r1
      + (T0 * (L0 * T0 ^ 2 + L1 * T1 ^ 2 + L2 * T2 ^ 2 + L3 * T3 ^ 2 + L4 * T4 ^ 2) / 2
        - 2 * L0 * T0 ^ 3) * r2)

set_option maxHeartbeats 800000 in
theorem Lam_star (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (v : (V4 Kf))
    (θ : Fin 5 → Kf) (hC : Chart N v θ) (Z : (M45 Kf)) (hZ : Z ∈ N) (σ : Equiv.Perm (Fin 5)) :
    lamL v Z (σ 0) * (cc (θ (σ 0)) * lamL v Z (σ 0) ^ 2 -
      (lamL v Z (σ 0) ^ 2 * kk (θ (σ 0)) (θ (σ 0)) + lamL v Z (σ 1) ^ 2 * kk (θ (σ 0)) (θ (σ 1))
        + lamL v Z (σ 2) ^ 2 * kk (θ (σ 0)) (θ (σ 2))
        + lamL v Z (σ 3) ^ 2 * kk (θ (σ 0)) (θ (σ 3))
        + lamL v Z (σ 4) ^ 2 * kk (θ (σ 0)) (θ (σ 4)))) = 0 := by
  obtain ⟨hk, h1, h2, h3, hcol⟩ := hC
  have e := sum_cols_perm σ Z
  rw [hrs Z hZ, hcol Z hZ (σ 0), hcol Z hZ (σ 1), hcol Z hZ (σ 2), hcol Z hZ (σ 3),
    hcol Z hZ (σ 4)] at e
  obtain ⟨r0, r1, r2⟩ := Uv_sum v hk h1 h2 h3 _ _ _ _ _ _ _ _ _ _ e
  have hS := SLev_perm σ N hN
  have hY : (cperm (Kf := Kf)) σ Z ∈ N.map ((cperm (Kf := Kf)) σ) := Submodule.mem_map_of_mem hZ
  have c0 := (C34 _ hS _ hY 0).2.1
  have c1 := (C34 _ hS _ hY 1).2.1
  have c2 := (C34 _ hS _ hY 2).2.1
  have c3 := (C34 _ hS _ hY 3).2.1
  have c4 := (C34 _ hS _ hY 4).2.1
  rw [sa0.1, sa0.2.1, sa0.2.2.1, sa0.2.2.2] at c0
  rw [sa1.1, sa1.2.1, sa1.2.2.1, sa1.2.2.2] at c1
  rw [sa2.1, sa2.2.1, sa2.2.2.1, sa2.2.2.2] at c2
  rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at c3
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at c4
  have hc : ∀ k, col ((cperm (Kf := Kf)) σ Z) k = lamL v Z (σ k) • Uv v (θ (σ k)) := fun k =>
    hcol Z hZ (σ k)
  simp only [hc, t3_smul3, t3_Uv v hk h1 h2 h3] at c0 c1 c2 c3 c4
  exact star_cert _ _ _ _ _ _ _ _ _ _ r0 r1 r2 (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) c0)
    (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) c1) (by linear_combination c2) (by linear_combination c3)
    (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) c4)

def Fq (θ : Fin 5 → Kf) (m : Fin 5) (lam : Fin 5 → Kf) : Kf :=
  cc (θ m) * lam m ^ 2 - ∑ n, lam n ^ 2 * kk (θ m) (θ n)

theorem sum5 (σ : Equiv.Perm (Fin 5)) (f : Fin 5 → Kf) :
    f (σ 0) + f (σ 1) + f (σ 2) + f (σ 3) + f (σ 4) = ∑ n, f n := by
  rw [← Equiv.sum_comp σ f, Fin.sum_univ_five]

theorem Fq_sigma (θ lam : Fin 5 → Kf) (m : Fin 5) (σ : Equiv.Perm (Fin 5)) :
    Fq θ m lam = cc (θ m) * lam m ^ 2 - (lam (σ 0) ^ 2 * kk (θ m) (θ (σ 0))
      + lam (σ 1) ^ 2 * kk (θ m) (θ (σ 1)) + lam (σ 2) ^ 2 * kk (θ m) (θ (σ 2))
      + lam (σ 3) ^ 2 * kk (θ m) (θ (σ 3)) + lam (σ 4) ^ 2 * kk (θ m) (θ (σ 4))) := by
  have e : lam (σ 0) ^ 2 * kk (θ m) (θ (σ 0))
      + lam (σ 1) ^ 2 * kk (θ m) (θ (σ 1)) + lam (σ 2) ^ 2 * kk (θ m) (θ (σ 2))
      + lam (σ 3) ^ 2 * kk (θ m) (θ (σ 3)) + lam (σ 4) ^ 2 * kk (θ m) (θ (σ 4)) =
      ∑ n, lam n ^ 2 * kk (θ m) (θ n) := sum5 σ (fun n => lam n ^ 2 * kk (θ m) (θ n))
  rw [e]
  rfl

set_option maxHeartbeats 800000 in
theorem Lam_F (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0) (v : (V4 Kf))
    (θ : Fin 5 → Kf) (hC : Chart N v θ) (z : (M45 Kf)) (hz : z ∈ N) (hz0 : ∀ m, lamL v z m ≠ 0)
    (Z : (M45 Kf)) (hZ : Z ∈ N) (m : Fin 5) : Fq θ m (lamL v Z) = 0 := by
  have star : ∀ Y ∈ N, lamL v Y m * Fq θ m (lamL v Y) = 0 := by
    intro Y hY
    have h := Lam_star N hN hrs v θ hC Y hY (Equiv.swap 0 m)
    rw [Fq_sigma θ (lamL v Y) m (Equiv.swap 0 m)]
    rw [Equiv.swap_apply_left] at h ⊢
    exact h
  by_cases h0 : lamL v Z m = 0
  · have e1 := star (Z + z) (N.add_mem hZ hz)
    have e2 := star (Z - z) (N.sub_mem hZ hz)
    have e3 := star z hz
    rw [map_add] at e1
    rw [map_sub] at e2
    have n1 : (lamL v Z + lamL v z) m ≠ 0 := by
      rw [Pi.add_apply, h0, zero_add]
      exact hz0 m
    have n2 : (lamL v Z - lamL v z) m ≠ 0 := by
      rw [Pi.sub_apply, h0, zero_sub]
      exact neg_ne_zero.mpr (hz0 m)
    have f1 := (mul_eq_zero.mp e1).resolve_left n1
    have f2 := (mul_eq_zero.mp e2).resolve_left n2
    have f3 := (mul_eq_zero.mp e3).resolve_left (hz0 m)
    have par : Fq θ m (lamL v Z + lamL v z) + Fq θ m (lamL v Z - lamL v z) =
        2 * Fq θ m (lamL v Z) + 2 * Fq θ m (lamL v z) := by
      simp only [Fq, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_five]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * (f1 + f2) - f3 - (1 / 2 : Kf) * par
  · exact (mul_eq_zero.mp (star Z hZ)).resolve_left h0

def AlgCore : Prop := ∀ (θ : Fin 5 → Kf) (Lam : Submodule Kf (Fin 5 → Kf)),
    2 ≤ Module.finrank Kf Lam →
    (∀ lam ∈ Lam, (∑ n, lam n = 0) ∧ (∑ n, lam n * θ n = 0) ∧ (∑ n, lam n * θ n ^ 2 = 0)) →
    (∀ lam ∈ Lam, ∀ m, Fq θ m lam = 0) →
    (∃ ζ ∈ Lam, ∀ m, ζ m ≠ 0) →
    (∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ θ a ≠ θ b ∧ θ a ≠ θ c ∧ θ b ≠ θ c) → False

set_option maxHeartbeats 800000 in
theorem HypS6_of [Fact (∃ i : Kf, i ^ 2 = -1)] (HA : (AlgCore (Kf := Kf))) : (HypS6 (Kf := Kf)) := by
  unfold HypS6
  intro N hN hrs hd z hz hmax a b c hab hac hbc hind hact
  obtain ⟨v, h1, h2, h3, hk, hnp⟩ := chart (fun m => col z m) hact
  have hzc : ∀ m, ∃ θ ζ : Kf, ζ ≠ 0 ∧ col z m = ζ • Uv v θ := fun m =>
    iso_coords v hk h1 h2 h3 (col z m) (C1 N hN z hz m) (Niso N hN hrs z z hz hz m) (hnp m)
  choose θ ζ hζ hzθ using hzc
  have hcol : ∀ Z ∈ N, ∀ m, col Z m = lamL v Z m • Uv v (θ m) := fun Z hZ m =>
    N_coords N z hmax v hk h1 h2 h3 θ ζ hzθ Z hZ m
  have hC : Chart N v θ := ⟨hk, h1, h2, h3, hcol⟩
  have hz0 : ∀ m, lamL v z m ≠ 0 := by
    intro m h0
    apply hact m
    rw [hcol z hz m, h0, zero_smul]
  have nab : θ a ≠ θ b := by
    intro h
    have e : ζ b • col z a + (-ζ a) • col z b + (0 : Kf) • col z c = 0 := by
      rw [hzθ a, hzθ b, h]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
    exact hζ b (hind _ _ _ e).1
  have nac : θ a ≠ θ c := by
    intro h
    have e : ζ c • col z a + (0 : Kf) • col z b + (-ζ a) • col z c = 0 := by
      rw [hzθ a, hzθ c, h]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
    exact hζ c (hind _ _ _ e).1
  have nbc : θ b ≠ θ c := by
    intro h
    have e : (0 : Kf) • col z a + ζ c • col z b + (-ζ b) • col z c = 0 := by
      rw [hzθ b, hzθ c, h]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
    exact hζ c (hind _ _ _ e).2.1
  have rn := rank_nullity N (lamL v)
  have hker : (N ⊓ LinearMap.ker (lamL v) : Submodule Kf (M45 Kf)) = ⊥ := by
    rw [eq_bot_iff]
    rintro Z ⟨hZ, hZk⟩
    rw [Submodule.mem_bot]
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hZk
    funext ⟨i, m⟩
    have h := congrFun (hcol Z hZ m) i
    rw [hZk, Pi.zero_apply, zero_smul] at h
    exact h
  rw [hker, finrank_bot] at rn
  apply HA θ (N.map (lamL v))
  · omega
  · rintro lam ⟨Z, hZ, rfl⟩
    exact Lam_rel N hrs v θ hC Z hZ
  · rintro lam ⟨Z, hZ, rfl⟩ m
    exact Lam_F N hN hrs v θ hC z hz hz0 Z hZ m
  · exact ⟨lamL v z, Submodule.mem_map_of_mem hz, hz0⟩
  · exact ⟨a, b, c, hab, hac, hbc, nab, nac, nbc⟩


def Good5 (T L : Fin 5 → Kf) : Prop :=
  (L 0 + L 1 + L 2 + L 3 + L 4 = 0) ∧
  (L 0 * T 0 + L 1 * T 1 + L 2 * T 2 + L 3 * T 3 + L 4 * T 4 = 0) ∧
  (L 0 * T 0 ^ 2 + L 1 * T 1 ^ 2 + L 2 * T 2 ^ 2 + L 3 * T 3 ^ 2 + L 4 * T 4 ^ 2 = 0) ∧
  ∀ j, cc (T j) * L j ^ 2 - (L 0 ^ 2 * kk (T j) (T 0) + L 1 ^ 2 * kk (T j) (T 1)
    + L 2 ^ 2 * kk (T j) (T 2) + L 3 ^ 2 * kk (T j) (T 3) + L 4 ^ 2 * kk (T j) (T 4)) = 0

set_option maxHeartbeats 800000 in
theorem singA (Z0 Z1 Z2 Z3 Z4 T0 T1 T2 T3 T4 : Kf) (r0 : Z0 + Z1 + Z2 + Z3 + Z4 = 0)
    (r1 : Z0 * T0 + Z1 * T1 + Z2 * T2 + Z3 * T3 + Z4 * T4 = 0)
    (r2 : Z0 * T0 ^ 2 + Z1 * T1 ^ 2 + Z2 * T2 ^ 2 + Z3 * T3 ^ 2 + Z4 * T4 ^ 2 = 0)
    (hZ : Z0 ≠ 0) (h1 : T0 ≠ T1) (h2 : T0 ≠ T2) (h3 : T3 = T1 ∨ T3 = T2)
    (h4 : T4 = T1 ∨ T4 = T2) : False := by
  have p3 : (T3 - T1) * (T3 - T2) = 0 := by
    rcases h3 with h | h
    · rw [h]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
    · rw [h]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  have p4 : (T4 - T1) * (T4 - T2) = 0 := by
    rcases h4 with h | h
    · rw [h]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
    · rw [h]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  have key : Z0 * ((T0 - T1) * (T0 - T2)) = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) r2 - (T1 + T2) * r1 + T1 * T2 * r0 - Z3 * p3 - Z4 * p4
  rcases mul_eq_zero.mp key with h | h
  · exact hZ h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact h1 (sub_eq_zero.mp h')
    · exact h2 (sub_eq_zero.mp h')

set_option maxHeartbeats 800000 in
theorem pairB (La Lb Lm Lx Ly Ta Tb Tm Tx Ty : Kf) (r0 : La + Lb + Lm + Lx + Ly = 0)
    (r1 : La * Ta + Lb * Tb + Lm * Tm + Lx * Tx + Ly * Ty = 0)
    (r2 : La * Ta ^ 2 + Lb * Tb ^ 2 + Lm * Tm ^ 2 + Lx * Tx ^ 2 + Ly * Ty ^ 2 = 0)
    (hLm : Lm = 0) (hne : ¬(La = 0 ∧ Lb = 0 ∧ Lx = 0 ∧ Ly = 0)) (eab : Ta = Tb)
    (d1 : Tb ≠ Tx) (d2 : Tb ≠ Ty) (d3 : Tx ≠ Ty) (d4 : Tm ≠ Tx) (d5 : Tm ≠ Ty)
    (Fm : cc Tm * Lm ^ 2 - (La ^ 2 * kk Tm Ta + Lb ^ 2 * kk Tm Tb + Lm ^ 2 * kk Tm Tm
      + Lx ^ 2 * kk Tm Tx + Ly ^ 2 * kk Tm Ty) = 0)
    (Fx : cc Tx * Lx ^ 2 - (La ^ 2 * kk Tx Ta + Lb ^ 2 * kk Tx Tb + Lm ^ 2 * kk Tx Tm
      + Lx ^ 2 * kk Tx Tx + Ly ^ 2 * kk Tx Ty) = 0)
    (Fy : cc Ty * Ly ^ 2 - (La ^ 2 * kk Ty Ta + Lb ^ 2 * kk Ty Tb + Lm ^ 2 * kk Ty Tm
      + Lx ^ 2 * kk Ty Tx + Ly ^ 2 * kk Ty Ty) = 0) : False := by
  have kx : Lx * ((Tx - Tb) * (Tx - Ty)) = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) r2 - (Tb + Ty) * r1 + Tb * Ty * r0 - La * (Ta - Ty) * eab
      - (Tm - Tb) * (Tm - Ty) * hLm
  have ky : Ly * ((Ty - Tb) * (Ty - Tx)) = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) r2 - (Tb + Tx) * r1 + Tb * Tx * r0 - La * (Ta - Tx) * eab
      - (Tm - Tb) * (Tm - Tx) * hLm
  have hx : Lx = 0 := by
    rcases mul_eq_zero.mp kx with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d1 (sub_eq_zero.mp h').symm).elim
      · exact (d3 (sub_eq_zero.mp h')).elim
  have hy : Ly = 0 := by
    rcases mul_eq_zero.mp ky with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d2 (sub_eq_zero.mp h').symm).elim
      · exact (d3 (sub_eq_zero.mp h').symm).elim
  have hb : Lb = -La := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) r0 - hLm - hx - hy
  have hLa : La ≠ 0 := by
    intro h
    exact hne ⟨h, by rw [hb, h, neg_zero], hx, hy⟩
  have gm : La ^ 2 * kk Tm Tb = 0 := by
    rw [hLm, hx, hy, hb, eab] at Fm
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 2 : Kf) * Fm
  have gx : La ^ 2 * kk Tx Tb = 0 := by
    rw [hLm, hx, hy, hb, eab] at Fx
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 2 : Kf) * Fx
  have gy : La ^ 2 * kk Ty Tb = 0 := by
    rw [hLm, hx, hy, hb, eab] at Fy
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 2 : Kf) * Fy
  have km := (mul_eq_zero.mp gm).resolve_left (pow_ne_zero 2 hLa)
  have kx' := (mul_eq_zero.mp gx).resolve_left (pow_ne_zero 2 hLa)
  have ky' := (mul_eq_zero.mp gy).resolve_left (pow_ne_zero 2 hLa)
  simp only [kk] at km kx' ky'
  have hA : Tb * (Tb * Tb) * ((Tm - Tx) * (Tm - Ty) * (Tx - Ty)) = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (Tx - Ty) * km - (Tm - Ty) * kx' + (Tm - Tx) * ky'
  rcases mul_eq_zero.mp hA with h | h
  · have hs : Tb = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact mul_self_eq_zero.mp h'
    rw [hs] at km kx'
    have h2 : (Tm - Tx) * 2 = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) km - kx'
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact d4 (sub_eq_zero.mp h')
    · exact two_ne_zero h'
  · rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact d4 (sub_eq_zero.mp h'')
      · exact d5 (sub_eq_zero.mp h'')
    · exact d3 (sub_eq_zero.mp h')

theorem inj5 (T : Fin 5 → Kf) (h01 : T 0 ≠ T 1) (h02 : T 0 ≠ T 2) (h03 : T 0 ≠ T 3)
    (h04 : T 0 ≠ T 4) (h12 : T 1 ≠ T 2) (h13 : T 1 ≠ T 3) (h14 : T 1 ≠ T 4) (h23 : T 2 ≠ T 3)
    (h24 : T 2 ≠ T 4) (h34 : T 3 ≠ T 4) : Function.Injective T := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | exact absurd h h01
    | exact absurd h.symm h01
    | exact absurd h h02
    | exact absurd h.symm h02
    | exact absurd h h03
    | exact absurd h.symm h03
    | exact absurd h h04
    | exact absurd h.symm h04
    | exact absurd h h12
    | exact absurd h.symm h12
    | exact absurd h h13
    | exact absurd h.symm h13
    | exact absurd h h14
    | exact absurd h.symm h14
    | exact absurd h h23
    | exact absurd h.symm h23
    | exact absurd h h24
    | exact absurd h.symm h24
    | exact absurd h h34
    | exact absurd h.symm h34

theorem Lam_peel (Lam : Submodule Kf (Fin 5 → Kf)) (hfr : 2 ≤ Module.finrank Kf Lam) (m : Fin 5) :
    ∃ lam ∈ Lam, lam m = 0 ∧ lam ≠ 0 := by
  have rn := rank_nullity Lam (LinearMap.proj m : (Fin 5 → Kf) →ₗ[Kf] Kf)
  have h1 : Module.finrank Kf (Lam.map (LinearMap.proj m : (Fin 5 → Kf) →ₗ[Kf] Kf)) ≤ 1 := by
    have h := Submodule.finrank_le (Lam.map (LinearMap.proj m : (Fin 5 → Kf) →ₗ[Kf] Kf))
    rw [Module.finrank_self] at h
    exact h
  have hne : (Lam ⊓ LinearMap.ker (LinearMap.proj m : (Fin 5 → Kf) →ₗ[Kf] Kf) :
      Submodule Kf (Fin 5 → Kf)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rn
    omega
  obtain ⟨lam, hlam, hne0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw := Submodule.mem_inf.mp hlam
  exact ⟨lam, hw.1, LinearMap.mem_ker.mp hw.2, hne0⟩

set_option maxHeartbeats 800000 in
theorem core5 (T : Fin 5 → Kf) (P : (Fin 5 → Kf) → Prop)
    (hgood : ∀ L, P L → Good5 T L)
    (hpeel : ∀ k : Fin 5, ∃ L, P L ∧ L k = 0 ∧ ¬ (∀ j, L j = 0))
    (hζ : ∃ L, P L ∧ ∀ j, L j ≠ 0)
    (h01 : T 0 ≠ T 1) (h02 : T 0 ≠ T 2) (h12 : T 1 ≠ T 2)
    (hC : Function.Injective T → False) : False := by
  obtain ⟨Z, hPZ, hZ⟩ := hζ
  obtain ⟨z0, z1, z2, _⟩ := hgood Z hPZ
  have tA0 : (T 3 = T 1 ∨ T 3 = T 2) → (T 4 = T 1 ∨ T 4 = T 2) → False := fun h3 h4 =>
    singA (Z 0) (Z 1) (Z 2) (Z 3) (Z 4) (T 0) (T 1) (T 2) (T 3) (T 4) z0 z1 z2 (hZ 0) h01 h02
      h3 h4
  have tA1 : (T 3 = T 0 ∨ T 3 = T 2) → (T 4 = T 0 ∨ T 4 = T 2) → False := fun h3 h4 =>
    singA (Z 1) (Z 0) (Z 2) (Z 3) (Z 4) (T 1) (T 0) (T 2) (T 3) (T 4)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) z0) (by linear_combination z1) (by linear_combination z2) (hZ 1)
      h01.symm h12 h3 h4
  have tA2 : (T 3 = T 0 ∨ T 3 = T 1) → (T 4 = T 0 ∨ T 4 = T 1) → False := fun h3 h4 =>
    singA (Z 2) (Z 0) (Z 1) (Z 3) (Z 4) (T 2) (T 0) (T 1) (T 3) (T 4)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) z0) (by linear_combination z1) (by linear_combination z2) (hZ 2)
      h02.symm h12.symm h3 h4
  obtain ⟨A, hPA, hA0, hAnz⟩ := hpeel 0
  obtain ⟨a0, a1, a2, aF⟩ := hgood A hPA
  obtain ⟨B, hPB, hB1, hBnz⟩ := hpeel 1
  obtain ⟨b0, b1, b2, bF⟩ := hgood B hPB
  by_cases m3 : T 3 = T 0 ∨ T 3 = T 1 ∨ T 3 = T 2
  · by_cases m4 : T 4 = T 0 ∨ T 4 = T 1 ∨ T 4 = T 2
    · rcases m3 with e3 | e3 | e3 <;> rcases m4 with e4 | e4 | e4
      · exact tA1 (Or.inl e3) (Or.inl e4)
      · exact tA2 (Or.inl e3) (Or.inr e4)
      · exact tA1 (Or.inl e3) (Or.inr e4)
      · exact tA2 (Or.inr e3) (Or.inl e4)
      · exact tA0 (Or.inl e3) (Or.inl e4)
      · exact tA0 (Or.inl e3) (Or.inr e4)
      · exact tA1 (Or.inr e3) (Or.inl e4)
      · exact tA0 (Or.inr e3) (Or.inl e4)
      · exact tA0 (Or.inr e3) (Or.inr e4)
    · have n40 : T 4 ≠ T 0 := fun h => m4 (Or.inl h)
      have n41 : T 4 ≠ T 1 := fun h => m4 (Or.inr (Or.inl h))
      have n42 : T 4 ≠ T 2 := fun h => m4 (Or.inr (Or.inr h))
      rcases m3 with e3 | e3 | e3
      · exact pairB (B 3) (B 0) (B 1) (B 2) (B 4) (T 3) (T 0) (T 1) (T 2) (T 4)
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) b0) (by linear_combination b1) (by linear_combination b2) hB1
          (fun h => hBnz (fin5 (fun j => B j = 0) h.2.1 hB1 h.2.2.1 h.1 h.2.2.2))
          e3 h02 n40.symm n42.symm h12 n41.symm
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) bF 1) (by linear_combination bF 2) (by linear_combination bF 4)
      · exact pairB (A 3) (A 1) (A 0) (A 2) (A 4) (T 3) (T 1) (T 0) (T 2) (T 4)
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.1 h.2.2.1 h.1 h.2.2.2))
          e3 h12 n41.symm n42.symm h02 n40.symm
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) aF 0) (by linear_combination aF 2) (by linear_combination aF 4)
      · exact pairB (A 3) (A 2) (A 0) (A 1) (A 4) (T 3) (T 2) (T 0) (T 1) (T 4)
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.2.1 h.2.1 h.1 h.2.2.2))
          e3 h12.symm n42.symm n41.symm h01 n40.symm
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) aF 0) (by linear_combination aF 1) (by linear_combination aF 4)
  · have n30 : T 3 ≠ T 0 := fun h => m3 (Or.inl h)
    have n31 : T 3 ≠ T 1 := fun h => m3 (Or.inr (Or.inl h))
    have n32 : T 3 ≠ T 2 := fun h => m3 (Or.inr (Or.inr h))
    by_cases m4 : T 4 = T 0 ∨ T 4 = T 1 ∨ T 4 = T 2
    · rcases m4 with e4 | e4 | e4
      · exact pairB (B 4) (B 0) (B 1) (B 2) (B 3) (T 4) (T 0) (T 1) (T 2) (T 3)
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) b0) (by linear_combination b1) (by linear_combination b2) hB1
          (fun h => hBnz (fin5 (fun j => B j = 0) h.2.1 hB1 h.2.2.1 h.2.2.2 h.1))
          e4 h02 n30.symm n32.symm h12 n31.symm
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) bF 1) (by linear_combination bF 2) (by linear_combination bF 3)
      · exact pairB (A 4) (A 1) (A 0) (A 2) (A 3) (T 4) (T 1) (T 0) (T 2) (T 3)
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.1 h.2.2.1 h.2.2.2 h.1))
          e4 h12 n31.symm n32.symm h02 n30.symm
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) aF 0) (by linear_combination aF 2) (by linear_combination aF 3)
      · exact pairB (A 4) (A 2) (A 0) (A 1) (A 3) (T 4) (T 2) (T 0) (T 1) (T 3)
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.2.1 h.2.1 h.2.2.2 h.1))
          e4 h12.symm n32.symm n31.symm h01 n30.symm
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) aF 0) (by linear_combination aF 1) (by linear_combination aF 3)
    · have n40 : T 4 ≠ T 0 := fun h => m4 (Or.inl h)
      have n41 : T 4 ≠ T 1 := fun h => m4 (Or.inr (Or.inl h))
      have n42 : T 4 ≠ T 2 := fun h => m4 (Or.inr (Or.inr h))
      by_cases e34 : T 3 = T 4
      · exact pairB (A 3) (A 4) (A 0) (A 1) (A 2) (T 3) (T 4) (T 0) (T 1) (T 2)
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a0) (by linear_combination a1) (by linear_combination a2) hA0
          (fun h => hAnz (fin5 (fun j => A j = 0) hA0 h.2.2.1 h.2.2.2 h.1 h.2.1))
          e34 n41 n42 h12 h01 h02
          (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) aF 0) (by linear_combination aF 1) (by linear_combination aF 2)
      · exact hC (inj5 T h01 h02 n30.symm n40.symm h12 n31.symm n41.symm n32.symm n42.symm e34)

def HypS6C : Prop := ∀ (θ : Fin 5 → Kf) (Lam : Submodule Kf (Fin 5 → Kf)),
    Function.Injective θ → 2 ≤ Module.finrank Kf Lam →
    (∀ lam ∈ Lam, (∑ n, lam n = 0) ∧ (∑ n, lam n * θ n = 0) ∧ (∑ n, lam n * θ n ^ 2 = 0)) →
    (∀ lam ∈ Lam, ∀ m, Fq θ m lam = 0) → False

theorem AlgCore_of (HC : (HypS6C (Kf := Kf))) : (AlgCore (Kf := Kf)) := by
  unfold AlgCore
  intro θ Lam hfr hrel hF hζ habc
  obtain ⟨a, b, c, hab, hac, hbc, tab, tac, tbc⟩ := habc
  obtain ⟨σ, s0, s1, s2⟩ := perm_three a b c hab hac hbc
  apply core5 (fun k => θ (σ k)) (fun L => ∃ lam ∈ Lam, L = fun k => lam (σ k))
  · rintro L ⟨lam, hlam, rfl⟩
    obtain ⟨R0, R1, R2⟩ := hrel lam hlam
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (sum5 σ lam).trans R0
    · exact (sum5 σ (fun n => lam n * θ n)).trans R1
    · exact (sum5 σ (fun n => lam n * θ n ^ 2)).trans R2
    · intro j
      have h := hF lam hlam (σ j)
      rw [Fq_sigma θ lam (σ j) σ] at h
      exact h
  · intro k
    obtain ⟨lam, hlam, hk0, hne⟩ := Lam_peel Lam hfr (σ k)
    refine ⟨fun j => lam (σ j), ⟨lam, hlam, rfl⟩, hk0, ?_⟩
    intro hall
    apply hne
    funext n
    have h2 : lam (σ (σ.symm n)) = 0 := hall (σ.symm n)
    rw [Equiv.apply_symm_apply] at h2
    exact h2
  · obtain ⟨ζ, hζL, hζ0⟩ := hζ
    exact ⟨fun j => ζ (σ j), ⟨ζ, hζL, rfl⟩, fun j => hζ0 (σ j)⟩
  · show θ (σ 0) ≠ θ (σ 1)
    rw [s0, s1]
    exact tab
  · show θ (σ 0) ≠ θ (σ 2)
    rw [s0, s2]
    exact tac
  · show θ (σ 1) ≠ θ (σ 2)
    rw [s1, s2]
    exact tbc
  · intro hT
    have hθ : Function.Injective θ := by
      intro n n' h
      have h' : (fun k => θ (σ k)) (σ.symm n) = (fun k => θ (σ k)) (σ.symm n') := by
        show θ (σ (σ.symm n)) = θ (σ (σ.symm n'))
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact h
      exact σ.symm.injective (hT h')
    exact HC θ Lam hθ hfr hrel hF


set_option maxHeartbeats 800000 in
def mom3 (θ : Fin 5 → Kf) : (Fin 5 → Kf) →ₗ[Kf] Kf where
  toFun lam := lam 0 * θ 0 ^ 3 + lam 1 * θ 1 ^ 3 + lam 2 * θ 2 ^ 3 + lam 3 * θ 3 ^ 3
    + lam 4 * θ 4 ^ 3
  map_add' a b := by
    simp only [Pi.add_apply]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

theorem mom3_apply (θ lam : Fin 5 → Kf) : mom3 θ lam = lam 0 * θ 0 ^ 3 + lam 1 * θ 1 ^ 3
    + lam 2 * θ 2 ^ 3 + lam 3 * θ 3 ^ 3 + lam 4 * θ 4 ^ 3 := rfl

theorem Lam_ker (Lam : Submodule Kf (Fin 5 → Kf)) (hfr : 2 ≤ Module.finrank Kf Lam)
    (f : (Fin 5 → Kf) →ₗ[Kf] Kf) : ∃ lam ∈ Lam, f lam = 0 ∧ lam ≠ 0 := by
  have rn := rank_nullity Lam f
  have h1 : Module.finrank Kf (Lam.map f) ≤ 1 := by
    have h := Submodule.finrank_le (Lam.map f)
    rw [Module.finrank_self] at h
    exact h
  have hne : (Lam ⊓ LinearMap.ker f : Submodule Kf (Fin 5 → Kf)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at rn
    omega
  obtain ⟨lam, hlam, hne0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw := Submodule.mem_inf.mp hlam
  exact ⟨lam, hw.1, LinearMap.mem_ker.mp hw.2, hne0⟩

set_option maxHeartbeats 800000 in
theorem vdm3 (x0 x1 x2 t0 t1 t2 : Kf) (h0 : x0 + x1 + x2 = 0)
    (h1 : x0 * t0 + x1 * t1 + x2 * t2 = 0)
    (h2 : x0 * t0 ^ 2 + x1 * t1 ^ 2 + x2 * t2 ^ 2 = 0)
    (d01 : t0 ≠ t1) (d02 : t0 ≠ t2) (d12 : t1 ≠ t2) : x0 = 0 ∧ x1 = 0 ∧ x2 = 0 := by
  have k0 : x0 * ((t0 - t1) * (t0 - t2)) = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h2 - (t1 + t2) * h1 + t1 * t2 * h0
  have k1 : x1 * ((t1 - t0) * (t1 - t2)) = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h2 - (t0 + t2) * h1 + t0 * t2 * h0
  have k2 : x2 * ((t2 - t0) * (t2 - t1)) = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h2 - (t0 + t1) * h1 + t0 * t1 * h0
  refine ⟨?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp k0 with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d01 (sub_eq_zero.mp h')).elim
      · exact (d02 (sub_eq_zero.mp h')).elim
  · rcases mul_eq_zero.mp k1 with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d01 (sub_eq_zero.mp h').symm).elim
      · exact (d12 (sub_eq_zero.mp h')).elim
  · rcases mul_eq_zero.mp k2 with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact (d02 (sub_eq_zero.mp h').symm).elim
      · exact (d12 (sub_eq_zero.mp h').symm).elim

set_option maxHeartbeats 800000 in
theorem roots5 (T : Fin 5 → Kf) (hT : Function.Injective T) (a0 a1 a2 a3 a4 : Kf)
    (h : ∀ i, a0 + a1 * T i + a2 * T i ^ 2 + a3 * T i ^ 3 + a4 * T i ^ 4 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 := by
  have hz : (![a0, a1, a2, a3, a4] : Fin 5 → Kf) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hT)
    funext i
    have hi := h i
    show ∑ j : Fin 5, Matrix.vandermonde T i j * (![a0, a1, a2, a3, a4] : Fin 5 → Kf) j = 0
    rw [Fin.sum_univ_five]
    show T i ^ 0 * a0 + T i ^ 1 * a1 + T i ^ 2 * a2 + T i ^ 3 * a3 + T i ^ 4 * a4 = 0
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hi
  exact ⟨congrFun hz 0, congrFun hz 1, congrFun hz 2, congrFun hz 3, congrFun hz 4⟩

theorem moments5 (T : Fin 5 → Kf) (hT : Function.Injective T) (X : Fin 5 → Kf)
    (h : ∀ j : Fin 5, ∑ i, X i * T i ^ (j : ℕ) = 0) : X = 0 := by
  apply Matrix.eq_zero_of_vecMul_eq_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hT)
  funext j
  show ∑ i : Fin 5, X i * Matrix.vandermonde T i j = 0
  exact h j

def pw (T W : Fin 5 → Kf) (j : ℕ) : Kf :=
  W 0 ^ 2 * T 0 ^ j + W 1 ^ 2 * T 1 ^ j + W 2 ^ 2 * T 2 ^ j + W 3 ^ 2 * T 3 ^ j
    + W 4 ^ 2 * T 4 ^ j

set_option maxHeartbeats 800000 in
theorem caseC_alg (T W : Fin 5 → Kf) (hT : Function.Injective T)
    (E1 : ∀ m, Fq T m W = 0) (E3 : ∀ m, Fq T m (fun n => T n * W n) = 0)
    (E12 : ∀ m, Fq T m (W + fun n => T n * W n) = 0) : ∀ n, W n = 0 := by
  have hD : ∀ m, 4 * pw T W 2 + (pw T W 5 / 2 - 2 * pw T W 1) * T m
      + (pw T W 4 / 2 - 2 * pw T W 0) * T m ^ 2 + (-pw T W 3) * T m ^ 3 + 0 * T m ^ 4 = 0 := by
    intro m
    have e1 := E1 m
    have e3 := E3 m
    have e12 := E12 m
    simp only [Fq, Fin.sum_univ_five, Pi.add_apply, cc, kk] at e1 e3 e12
    simp only [pw]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) T m * e1 - (1 / 2 : Kf) * (e12 - e1 - e3)
  have hE : ∀ m, 4 * pw T W 3 + (2 * pw T W 2 + pw T W 6 / 2) * T m
      + (pw T W 5 - 4 * pw T W 1) * T m ^ 2 + (-2 * pw T W 0 - pw T W 4 / 2) * T m ^ 3
      + (-pw T W 3) * T m ^ 4 = 0 := by
    intro m
    have e1 := E1 m
    have e3 := E3 m
    simp only [Fq, Fin.sum_univ_five, cc, kk] at e1 e3
    simp only [pw]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) T m ^ 2 * e1 - e3
  obtain ⟨d0, d1, d2, d3, _⟩ := roots5 T hT _ _ _ _ _ hD
  obtain ⟨_, _, _, g3, _⟩ := roots5 T hT _ _ _ _ _ hE
  have q0 : pw T W 0 = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 4 : Kf) * (d2 + g3)
  have q4 : pw T W 4 = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) d2 - g3
  have q2 : pw T W 2 = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * d0
  have q3 : pw T W 3 = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * d3
  have q1 : pw T W 1 = 0 := by
    have s0 := E1 0
    have s1 := E1 1
    have s2 := E1 2
    have s3 := E1 3
    have s4 := E1 4
    simp only [Fq, Fin.sum_univ_five, cc, kk] at s0 s1 s2 s3 s4
    simp only [pw] at q0 q3 q4 d1 ⊢
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (s0 + s1 + s2 + s3 + s4) - (3 / 2 : Kf) * d1
      + ((T 0 + T 1 + T 2 + T 3 + T 4) / 2) * q0
      + ((T 0 ^ 2 + T 1 ^ 2 + T 2 ^ 2 + T 3 ^ 2 + T 4 ^ 2) / 4) * q3
      + ((T 0 + T 1 + T 2 + T 3 + T 4) / 8) * q4
  simp only [pw] at q0 q1 q2 q3 q4
  have m0 : ∑ i : Fin 5, (W i * W i) * T i ^ 0 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) q0
  have m1 : ∑ i : Fin 5, (W i * W i) * T i ^ 1 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) q1
  have m2 : ∑ i : Fin 5, (W i * W i) * T i ^ 2 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) q2
  have m3 : ∑ i : Fin 5, (W i * W i) * T i ^ 3 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) q3
  have m4 : ∑ i : Fin 5, (W i * W i) * T i ^ 4 = 0 := by
    rw [Fin.sum_univ_five]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) q4
  have hX : (fun n => W n * W n) = 0 :=
    moments5 T hT (fun n => W n * W n)
      (fin5 (fun j : Fin 5 => ∑ i, (fun n => W n * W n) i * T i ^ (j : ℕ) = 0) m0 m1 m2 m3 m4)
  intro n
  have h2 : W n * W n = 0 := congrFun hX n
  exact mul_self_eq_zero.mp h2

set_option maxHeartbeats 800000 in
theorem HypS6C_proof : (HypS6C (Kf := Kf)) := by
  unfold HypS6C
  intro θ Lam hθ hfr hrel hF
  have d01 : θ 0 ≠ θ 1 := hθ.ne (by decide)
  have d02 : θ 0 ≠ θ 2 := hθ.ne (by decide)
  have d12 : θ 1 ≠ θ 2 := hθ.ne (by decide)
  obtain ⟨w, hwL, hw3, hwne⟩ := Lam_ker Lam hfr (mom3 θ)
  rw [mom3_apply] at hw3
  obtain ⟨w0, w1, w2⟩ := hrel w hwL
  rw [Fin.sum_univ_five] at w0 w1 w2
  obtain ⟨A, hAL, hA3, hAne⟩ := Lam_peel Lam hfr 3
  obtain ⟨a0, a1, a2⟩ := hrel A hAL
  rw [Fin.sum_univ_five] at a0 a1 a2
  have hA4 : A 4 ≠ 0 := by
    intro h
    obtain ⟨e0, e1, e2⟩ := vdm3 (A 0) (A 1) (A 2) (θ 0) (θ 1) (θ 2)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a0 - hA3 - h)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a1 - θ 3 * hA3 - θ 4 * h)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) a2 - θ 3 ^ 2 * hA3 - θ 4 ^ 2 * h) d01 d02 d12
    apply hAne
    funext n
    exact fin5 (fun n => A n = 0) e0 e1 e2 hA3 h n
  obtain ⟨B, hBL, hB4, hBne⟩ := Lam_peel Lam hfr 4
  obtain ⟨b0, b1, b2⟩ := hrel B hBL
  rw [Fin.sum_univ_five] at b0 b1 b2
  have hB3 : B 3 ≠ 0 := by
    intro h
    obtain ⟨e0, e1, e2⟩ := vdm3 (B 0) (B 1) (B 2) (θ 0) (θ 1) (θ 2)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) b0 - h - hB4)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) b1 - θ 3 * h - θ 4 * hB4)
      (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) b2 - θ 3 ^ 2 * h - θ 4 ^ 2 * hB4) d01 d02 d12
    apply hBne
    funext n
    exact fin5 (fun n => B n = 0) e0 e1 e2 h hB4 n
  obtain ⟨cA, hcA⟩ : ∃ c : Kf, c * A 4 = θ 4 * w 4 :=
    ⟨θ 4 * w 4 / A 4, div_mul_cancel₀ _ hA4⟩
  obtain ⟨cB, hcB⟩ : ∃ c : Kf, c * B 3 = θ 3 * w 3 :=
    ⟨θ 3 * w 3 / B 3, div_mul_cancel₀ _ hB3⟩
  have hxL : cA • A + cB • B ∈ Lam := Lam.add_mem (Lam.smul_mem cA hAL) (Lam.smul_mem cB hBL)
  obtain ⟨x0, x1, x2⟩ := hrel _ hxL
  rw [Fin.sum_univ_five] at x0 x1 x2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at x0 x1 x2
  obtain ⟨e0, e1, e2⟩ := vdm3 (cA * A 0 + cB * B 0 - θ 0 * w 0)
    (cA * A 1 + cB * B 1 - θ 1 * w 1) (cA * A 2 + cB * B 2 - θ 2 * w 2) (θ 0) (θ 1) (θ 2)
    (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) x0 - w1 - cA * hA3 - hcB - hcA - cB * hB4)
    (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) x1 - w2 - θ 3 * (cA * hA3 + hcB) - θ 4 * (hcA + cB * hB4))
    (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) x2 - hw3 - θ 3 ^ 2 * (cA * hA3 + hcB) - θ 4 ^ 2 * (hcA + cB * hB4))
    d01 d02 d12
  have hxeq : cA • A + cB • B = fun n => θ n * w n := by
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact fin5 (fun n => cA * A n + cB * B n = θ n * w n)
      (by
        show cA * A 0 + cB * B 0 = θ 0 * w 0
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) e0)
      (by
        show cA * A 1 + cB * B 1 = θ 1 * w 1
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) e1)
      (by
        show cA * A 2 + cB * B 2 = θ 2 * w 2
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) e2)
      (by
        show cA * A 3 + cB * B 3 = θ 3 * w 3
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) cA * hA3 + hcB)
      (by
        show cA * A 4 + cB * B 4 = θ 4 * w 4
        linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hcA + cB * hB4) n
  have hxL' : (fun n => θ n * w n) ∈ Lam := by
    rw [← hxeq]
    exact hxL
  have hW := caseC_alg θ w hθ (fun m => hF w hwL m) (fun m => hF _ hxL' m)
    (fun m => hF _ (Lam.add_mem hwL hxL') m)
  apply hwne
  funext n
  exact hW n

theorem HypS6_proof [Fact (∃ i : Kf, i ^ 2 = -1)] : (HypS6 (Kf := Kf)) := HypS6_of (AlgCore_of (HypS6C_proof (Kf := Kf)))

def e2 (d : (V4 Kf)) : Kf := (tau d ^ 2 - ip d d) / 2

end

end PEqualNP.Outside.L_gct_210_aux.FLK

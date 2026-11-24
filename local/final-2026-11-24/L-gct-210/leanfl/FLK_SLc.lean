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

def indep (v w : (V4 Kf)) : Prop := ∀ s t : Kf, s • v + t • w = 0 → s = 0 ∧ t = 0

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

theorem sum_cols_perm (σ : Equiv.Perm (Fin 5)) (Z : (M45 Kf)) :
    col Z (σ 0) + col Z (σ 1) + col Z (σ 2) + col Z (σ 3) + col Z (σ 4) = (rs (Kf := Kf)) Z := by
  have h : ∑ j, col Z (σ j) = ∑ j, col Z j := Equiv.sum_comp σ (fun j => col Z j)
  rw [Fin.sum_univ_five, Fin.sum_univ_five] at h
  rw [h]
  funext i
  simp only [Pi.add_apply, col, rs_apply]

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

theorem indep_symm {v w : (V4 Kf)} (h : indep v w) : indep w v := fun s t e => by
  have h1 := h t s (by rw [add_comm]; exact e)
  exact ⟨h1.2, h1.1⟩

def swp : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem swp0 : swp 0 = 2 := by decide

theorem swp1 : swp 1 = 3 := by decide

theorem swp2 : swp 2 = 0 := by decide

theorem swp3 : swp 3 = 1 := by decide

theorem swp4 : swp 4 = 4 := by decide

theorem cols_zero (σ : Equiv.Perm (Fin 5)) (Z : (M45 Kf)) (h : ∀ j, col Z (σ j) = 0) : Z = 0 := by
  funext ⟨i, m⟩
  have hh := congrFun (h (σ.symm m)) i
  rw [Equiv.apply_symm_apply] at hh
  exact hh

theorem SLev_N (K : Submodule Kf (M45 Kf)) (hK : SLev K) :
    SLev (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) :=
  fun Y hY a => hK Y (Submodule.mem_inf.mp hY).1 a

theorem rs_N (K : Submodule Kf (M45 Kf)) :
    ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), (rs (Kf := Kf)) Z = 0 :=
  fun _ hZ => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hZ).2

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

set_option maxHeartbeats 800000 in
theorem S7_elem (N : Submodule Kf (M45 Kf)) (hN : SLev N) (hrs : ∀ Z ∈ N, (rs (Kf := Kf)) Z = 0)
    (hd : Module.finrank Kf N = 2) (z : (M45 Kf))
    (hmax : ∀ Z ∈ N, ∀ m, ∃ c : Kf, col Z m = c • col z m) (σ : Equiv.Perm (Fin 5)) (v w : (V4 Kf))
    (hi : indep v w) (c1 : col z (σ 1) = (-1 : Kf) • v)
    (c2 : col z (σ 2) = w) (c3 : col z (σ 3) = (-1 : Kf) • w) (c4 : col z (σ 4) = 0) :
    ∃ W ∈ N, col W (σ 0) = 0 ∧ col W (σ 1) = 0 ∧ col W (σ 2) = w ∧
      col W (σ 3) = (-1 : Kf) • w := by
  have p := peel N hN hrs (σ 0)
  have hne : (N ⊓ LinearMap.ker ((colL (Kf := Kf)) (σ 0)) : Submodule Kf (M45 Kf)) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at p
    omega
  obtain ⟨W0, hW0, hW0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw := Submodule.mem_inf.mp hW0
  have hWN := hw.1
  have a0 : col W0 (σ 0) = 0 := LinearMap.mem_ker.mp hw.2
  obtain ⟨k1, a1⟩ := hmax W0 hWN (σ 1)
  obtain ⟨k2, a2⟩ := hmax W0 hWN (σ 2)
  obtain ⟨k3, a3⟩ := hmax W0 hWN (σ 3)
  obtain ⟨k4, a4⟩ := hmax W0 hWN (σ 4)
  rw [c1] at a1
  rw [c2] at a2
  rw [c3] at a3
  rw [c4, smul_zero] at a4
  have hsum := sum_cols_perm σ W0
  rw [a0, a1, a2, a3, a4, hrs W0 hWN] at hsum
  have hk := hi (-k1) (k2 - k3) (by
    funext i
    have hi' := congrFun hsum i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi' ⊢
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hi')
  have hk1 : k1 = 0 := neg_eq_zero.mp hk.1
  have hk3 : k3 = k2 := (sub_eq_zero.mp hk.2).symm
  have hk2 : k2 ≠ 0 := by
    intro h
    apply hW0ne
    apply cols_zero σ
    apply fin5
    · exact a0
    · rw [a1, hk1, zero_smul]
    · rw [a2, h, zero_smul]
    · rw [a3, hk3, h, zero_smul]
    · exact a4
  refine ⟨k2⁻¹ • W0, N.smul_mem _ hWN, ?_, ?_, ?_, ?_⟩
  · show k2⁻¹ • col W0 (σ 0) = 0
    rw [a0, smul_zero]
  · show k2⁻¹ • col W0 (σ 1) = 0
    rw [a1, hk1, zero_smul, smul_zero]
  · show k2⁻¹ • col W0 (σ 2) = w
    rw [a2, smul_smul, inv_mul_cancel₀ hk2, one_smul]
  · show k2⁻¹ • col W0 (σ 3) = (-1 : Kf) • w
    rw [a3, hk3, smul_smul, inv_mul_cancel₀ hk2, one_smul]

set_option maxHeartbeats 800000 in
theorem S7_step (K : Submodule Kf (M45 Kf)) (hK : SLev K) (Yu : (M45 Kf)) (hYu : Yu ∈ K)
    (hu : ip ((rs (Kf := Kf)) Yu) ((rs (Kf := Kf)) Yu) = 0)
    (hd : Module.finrank Kf (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) = 2) (z : (M45 Kf))
    (hz : z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)))
    (hmax : ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), ∀ m, ∃ c : Kf,
      col Z m = c • col z m)
    (σ : Equiv.Perm (Fin 5)) (v w : (V4 Kf)) (hi : indep v w) (c0 : col z (σ 0) = v)
    (c1 : col z (σ 1) = (-1 : Kf) • v) (c2 : col z (σ 2) = w)
    (c3 : col z (σ 3) = (-1 : Kf) • w) (c4 : col z (σ 4) = 0) (hvww : t3 v w w = 0) :
    t3 ((rs (Kf := Kf)) Yu) w w = 0 := by
  have hNs := SLev_N K hK
  have hrsN := rs_N K
  obtain ⟨W, hWN, w0, w1, w2, w3⟩ := S7_elem _ hNs hrsN hd z hmax σ v w hi c1 c2 c3 c4
  have hWK : W ∈ K := (Submodule.mem_inf.mp hWN).1
  have hKσ := SLev_perm σ K hK
  have kp := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.add_mem hYu hWK)) 4).2.1
  have km := (C34 _ hKσ _ (Submodule.mem_map_of_mem (K.sub_mem hYu hWK)) 4).2.1
  have k0 := (C34 _ hKσ _ (Submodule.mem_map_of_mem hYu) 4).2.1
  rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at kp km k0
  have e0 : ∀ i, W (i, σ 0) = 0 := fun i => congrFun w0 i
  have e1 : ∀ i, W (i, σ 1) = 0 := fun i => congrFun w1 i
  have e2 : ∀ i, W (i, σ 2) = w i := fun i => congrFun w2 i
  have e3 : ∀ i, W (i, σ 3) = -1 * w i := fun i => congrFun w3 i
  simp only [t3, col, cperm_apply, Pi.add_apply, Pi.sub_apply, e0, e1, e2, e3] at kp km k0
  have hc : t3 (col Yu (σ 0)) w w + t3 (col Yu (σ 1)) w w = 0 := by
    simp only [t3, col]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 2 : Kf) * (kp + km - 2 * k0)
  have hv0 : v ≠ 0 := by
    intro h
    have h1 := (hi 1 0 (by rw [h]; simp)).1
    exact one_ne_zero h1
  have hz0 : col z (σ 0) ≠ 0 := by
    rw [c0]
    exact hv0
  have hz1 : col z (σ 1) ≠ 0 := by
    rw [c1]
    intro h
    exact hv0 ((smul_eq_zero.mp h).resolve_left (by norm_num))
  obtain ⟨β0, hβ0⟩ := Biii K hK Yu hYu hu z hz (σ 0) hz0
  obtain ⟨β1, hβ1⟩ := Biii K hK Yu hYu hu z hz (σ 1) hz1
  rw [c0] at hβ0
  rw [c1] at hβ1
  have f0 : ∀ i, 2 * Yu (i, σ 0) - (rs (Kf := Kf)) Yu i = β0 * v i := fun i => congrFun hβ0 i
  have f1 : ∀ i, 2 * Yu (i, σ 1) - (rs (Kf := Kf)) Yu i = β1 * (-1 * v i) := fun i => congrFun hβ1 i
  have f00 := f0 0
  have f01 := f0 1
  have f02 := f0 2
  have f03 := f0 3
  have f10 := f1 0
  have f11 := f1 1
  have f12 := f1 2
  have f13 := f1 3
  simp only [t3, col] at hc hvww ⊢
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hc
    - (1 / 2 : Kf) * (w 0 * w 0 * f00 + w 1 * w 1 * f01 + w 2 * w 2 * f02 + w 3 * w 3 * f03)
    - (1 / 2 : Kf) * (w 0 * w 0 * f10 + w 1 * w 1 * f11 + w 2 * w 2 * f12 + w 3 * w 3 * f13)
    - ((β0 - β1) / 2) * hvww

def HypS7alg : Prop :=
  ∀ v w u : (V4 Kf), tau v = 0 → ip v v = 0 → tau w = 0 → ip w w = 0 → indep v w →
    t3 v w w = 0 → t3 v v w = 0 → br v v w w = 0 →
    u ≠ 0 → tau u = 0 → ip u u = 0 → t3 u v v = 0 → t3 u w w = 0 → False

set_option maxHeartbeats 800000 in
theorem HypS7_of (h : (HypS7alg (Kf := Kf))) : (HypS7 (Kf := Kf)) := by
  unfold HypS7
  intro K hK hq hu hd z hz hmax σ hind e1 e3 e4 i1 i2 i3
  obtain ⟨u, huS, hu0, huperp⟩ := hu
  obtain ⟨Yu, hYu, rfl⟩ := huS
  have huu : ip ((rs (Kf := Kf)) Yu) ((rs (Kf := Kf)) Yu) = 0 := huperp _ (Submodule.mem_map_of_mem hYu)
  have hzK := (Submodule.mem_inf.mp hz).1
  have s1 := S7_step K hK Yu hYu huu hd z hz hmax σ (col z (σ 0)) (col z (σ 2)) hind rfl e1
    rfl e3 e4 i1
  have s2 := S7_step K hK Yu hYu huu hd z hz hmax (σ * swp) (col z (σ 2)) (col z (σ 0))
    ((indep_symm (Kf := Kf)) hind)
    (by rw [Equiv.Perm.mul_apply, swp0])
    (by rw [Equiv.Perm.mul_apply, swp1, e3])
    (by rw [Equiv.Perm.mul_apply, swp2])
    (by rw [Equiv.Perm.mul_apply, swp3, e1])
    (by rw [Equiv.Perm.mul_apply, swp4, e4])
    (by
      simp only [t3] at i2 ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) i2)
  exact h (col z (σ 0)) (col z (σ 2)) ((rs (Kf := Kf)) Yu) (C1 K hK z hzK (σ 0))
    (N_iso K hK z z hz hz (σ 0)) (C1 K hK z hzK (σ 2)) (N_iso K hK z z hz hz (σ 2)) hind
    i1 i2 i3 hu0 (tau_rs K hK Yu hYu) huu s2 s1

def HypIIa : Prop :=
  ∀ v w : (V4 Kf), tau v = 0 → ip v v = 0 → tau w = 0 → ip w w = 0 → indep v w →
    t3 v w w = 0 → t3 v v w = 0 → br v v w w = 0 →
    (∃ c : Kf, (fun i => v i * v i : (V4 Kf)) = c • w) ∧ (∃ c : Kf, (fun i => w i * w i : (V4 Kf)) = c • v)

set_option maxHeartbeats 800000 in
theorem HypS7alg_of (h : (HypIIa (Kf := Kf))) : (HypS7alg (Kf := Kf)) := by
  unfold HypS7alg
  intro v w u hv1 hv2 hw1 hw2 hind i1 i2 i3 hu0 hu1 hu2 j1 j2
  obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := h v w hv1 hv2 hw1 hw2 hind i1 i2 i3
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 := (hind 1 0 (by rw [h0]; simp)).1
    exact one_ne_zero h1
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 := (hind 0 1 (by rw [h0]; simp)).2
    exact one_ne_zero h1
  have hc0 : c ≠ 0 := by
    intro h0
    apply hv0
    funext i
    have hi := congrFun hc i
    rw [h0, zero_smul] at hi
    exact mul_self_eq_zero.mp hi
  have hc0' : c' ≠ 0 := by
    intro h0
    apply hw0
    funext i
    have hi := congrFun hc' i
    rw [h0, zero_smul] at hi
    exact mul_self_eq_zero.mp hi
  have huw : ip u w = 0 := by
    have e : c * ip u w = 0 := by
      have q0 := congrFun hc 0
      have q1 := congrFun hc 1
      have q2 := congrFun hc 2
      have q3 := congrFun hc 3
      simp only [Pi.smul_apply, smul_eq_mul] at q0 q1 q2 q3
      simp only [t3, ip] at j1 ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) j1 - u 0 * q0 - u 1 * q1 - u 2 * q2 - u 3 * q3
    exact (mul_eq_zero.mp e).resolve_left hc0
  have huv : ip u v = 0 := by
    have e : c' * ip u v = 0 := by
      have q0 := congrFun hc' 0
      have q1 := congrFun hc' 1
      have q2 := congrFun hc' 2
      have q3 := congrFun hc' 3
      simp only [Pi.smul_apply, smul_eq_mul] at q0 q1 q2 q3
      simp only [t3, ip] at j2 ⊢
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) j2 - u 0 * q0 - u 1 * q1 - u 2 * q2 - u 3 * q3
    exact (mul_eq_zero.mp e).resolve_left hc0'
  obtain ⟨k, hk⟩ := Q4 u v hu0 hu1 hu2 hv1 hv2 huv
  obtain ⟨k', hk'⟩ := Q4 u w hu0 hu1 hu2 hw1 hw2 huw
  have hkk := hind k' (-k) (by
    rw [hk, hk']
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf))
  apply hw0
  rw [hk', hkk.1, zero_smul]

set_option maxHeartbeats 800000 in
theorem IIa_tu (t u : Kf) (htu : t ≠ u)
    (E1 : 2 * u + t + t * u ^ 4 / 4 + t ^ 2 * u ^ 3 / 2 = 0)
    (E2 : 2 * t + u + u * t ^ 4 / 4 + u ^ 2 * t ^ 3 / 2 = 0)
    (B : 8 * (t - u) ^ 4
      - 24 * ((1 + t ^ 4 / 4) * (1 + u ^ 4 / 4) - 2 * t * u * (t ^ 2 + u ^ 2)) = 0) :
    4 + t ^ 4 + 4 * t ^ 3 * u = 0 ∧ t ^ 2 * u ^ 2 = 4 := by
  have hD : (u - t) * (4 + (t + u) ^ 2 * (t * u) + (t * u) ^ 2) = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) 4 * E1 - 4 * E2
  have h1 : 4 + (t + u) ^ 2 * (t * u) + (t * u) ^ 2 = 0 :=
    (mul_eq_zero.mp hD).resolve_left (sub_ne_zero.mpr (Ne.symm htu))
  have hS : (t + u) * (12 + (t + u) ^ 2 * (t * u) - (t * u) ^ 2) = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) 4 * E1 + 4 * E2
  rcases mul_eq_zero.mp hS with ha | h2
  · exfalso
    have hu : u = -t := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) ha
    subst hu
    have h128 : (128 : Kf) = 0 := by
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 : Kf) * B + (32 - (3 / 2 : Kf) * (t ^ 4 + 4)) * h1
    norm_num at h128
  · have hb : t ^ 2 * u ^ 2 = 4 := by
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * h1 - (1 / 2 : Kf) * h2
    refine ⟨?_, hb⟩
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (t * u) * t ^ 2 * h1
      - ((3 / 4 : Kf) * (t * u) * t ^ 2 + (1 / 4 : Kf) * (t ^ 4 + (t * u) ^ 2 + 4)) * hb

def Ps4 (j a0 a1 a2 a3 : Kf) : (V4 Kf) :=
  ![a0 + a1 + a2 + a3, a0 + a1 * j - a2 - a3 * j, a0 - a1 + a2 - a3, a0 - a1 * j - a2 + a3 * j]

theorem Ps4_0 (j a0 a1 a2 a3 : Kf) : Ps4 j a0 a1 a2 a3 0 = a0 + a1 + a2 + a3 := rfl

theorem Ps4_1 (j a0 a1 a2 a3 : Kf) : Ps4 j a0 a1 a2 a3 1 = a0 + a1 * j - a2 - a3 * j := rfl

theorem Ps4_2 (j a0 a1 a2 a3 : Kf) : Ps4 j a0 a1 a2 a3 2 = a0 - a1 + a2 - a3 := rfl

theorem Ps4_3 (j a0 a1 a2 a3 : Kf) : Ps4 j a0 a1 a2 a3 3 = a0 - a1 * j - a2 + a3 * j := rfl

set_option maxHeartbeats 800000 in
theorem tau_Ps4 (j a0 a1 a2 a3 : Kf) : tau (Ps4 j a0 a1 a2 a3) = 4 * a0 := by
  simp only [tau, Ps4_0, Ps4_1, Ps4_2, Ps4_3]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem Ps4_mul (j : Kf) (hj : j * j = -1) (a0 a1 a2 a3 b0 b1 b2 b3 : Kf) :
    (fun i => Ps4 j a0 a1 a2 a3 i * Ps4 j b0 b1 b2 b3 i : (V4 Kf)) =
      Ps4 j (a0 * b0 + a1 * b3 + a2 * b2 + a3 * b1) (a0 * b1 + a1 * b0 + a2 * b3 + a3 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a3 * b3) (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  funext i
  fin_cases i
  · show Ps4 j a0 a1 a2 a3 0 * Ps4 j b0 b1 b2 b3 0 = Ps4 j _ _ _ _ 0
    simp only [Ps4_0]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  · show Ps4 j a0 a1 a2 a3 1 * Ps4 j b0 b1 b2 b3 1 = Ps4 j _ _ _ _ 1
    simp only [Ps4_1]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (a1 - a3) * (b1 - b3) * hj
  · show Ps4 j a0 a1 a2 a3 2 * Ps4 j b0 b1 b2 b3 2 = Ps4 j _ _ _ _ 2
    simp only [Ps4_2]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  · show Ps4 j a0 a1 a2 a3 3 * Ps4 j b0 b1 b2 b3 3 = Ps4 j _ _ _ _ 3
    simp only [Ps4_3]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (a1 - a3) * (b1 - b3) * hj

theorem ip_Ps4 (j : Kf) (hj : j * j = -1) (a0 a1 a2 a3 b0 b1 b2 b3 : Kf) :
    ip (Ps4 j a0 a1 a2 a3) (Ps4 j b0 b1 b2 b3) =
      4 * (a0 * b0 + a1 * b3 + a2 * b2 + a3 * b1) := by
  have e : ip (Ps4 j a0 a1 a2 a3) (Ps4 j b0 b1 b2 b3) =
      tau (fun i => Ps4 j a0 a1 a2 a3 i * Ps4 j b0 b1 b2 b3 i : (V4 Kf)) := by
    simp only [ip, tau]
  rw [e, Ps4_mul j hj, tau_Ps4]

set_option maxHeartbeats 800000 in
theorem Ps4_param (j : Kf) (hj : j * j = -1) (v : (V4 Kf)) (hv : tau v = 0) :
    v = Ps4 j 0 ((v 0 - j * v 1 - v 2 + j * v 3) / 4) ((v 0 - v 1 + v 2 - v 3) / 4)
      ((v 0 + j * v 1 - v 2 - j * v 3) / 4) := by
  simp only [tau] at hv
  funext i
  fin_cases i
  · show v 0 = Ps4 j _ _ _ _ 0
    simp only [Ps4_0]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hv
  · show v 1 = Ps4 j _ _ _ _ 1
    simp only [Ps4_1]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hv - ((v 3 - v 1) / 2) * hj
  · show v 2 = Ps4 j _ _ _ _ 2
    simp only [Ps4_2]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hv
  · show v 3 = Ps4 j _ _ _ _ 3
    simp only [Ps4_3]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hv + ((v 3 - v 1) / 2) * hj

set_option maxHeartbeats 800000 in
theorem t3_ip_r (x y z : (V4 Kf)) : t3 x y z = ip x (fun i => y i * z i : (V4 Kf)) := by
  simp only [t3, ip]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

theorem t3_ip_l (x y z : (V4 Kf)) : t3 x y z = ip (fun i => x i * y i : (V4 Kf)) z := by
  simp only [t3, ip]

set_option maxHeartbeats 800000 in
theorem t4_ip (x y z w : (V4 Kf)) :
    t4 x y z w = ip (fun i => x i * y i : (V4 Kf)) (fun i => z i * w i : (V4 Kf)) := by
  simp only [t4, ip]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem IIa_pqr (p1 q1 r1 p2 q2 r2 : Kf) (iv : 2 * p1 * r1 + q1 ^ 2 = 0)
    (iw : 2 * p2 * r2 + q2 ^ 2 = 0)
    (T1 : 2 * p1 * p2 * q2 + q1 * (p2 ^ 2 + r2 ^ 2) + 2 * r1 * q2 * r2 = 0)
    (T2 : 2 * p2 * p1 * q1 + q2 * (p1 ^ 2 + r1 ^ 2) + 2 * r2 * q1 * r1 = 0)
    (Bq : -24 * (4 * q1 * r1 * p2 * q2 + (p1 ^ 2 + r1 ^ 2) * (p2 ^ 2 + r2 ^ 2)
      + 4 * p1 * q1 * q2 * r2) + 32 * (p1 * r2 + q1 * q2 + r1 * p2) ^ 2 = 0)
    (hnp : ∀ s t : Kf, s * p1 + t * p2 = 0 → s * q1 + t * q2 = 0 → s * r1 + t * r2 = 0 →
      s = 0 ∧ t = 0) :
    ∃ c : Kf, 2 * q1 * r1 = c * p2 ∧ p1 ^ 2 + r1 ^ 2 = c * q2 ∧ 2 * p1 * q1 = c * r2 := by
  by_cases hp1 : p1 = 0
  · exfalso
    subst hp1
    have hq1 : q1 = 0 := by
      have h : q1 ^ 2 = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) iv
      exact (pow_eq_zero_iff (by norm_num)).mp h
    subst hq1
    have hr1 : r1 ≠ 0 := by
      intro h
      have h1 := (hnp 1 0 (by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)) (by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)) (by rw [h]; (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf))).1
      exact one_ne_zero h1
    have hq2 : q2 = 0 := by
      have h : q2 * r1 ^ 2 = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) T2
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hr1)
    subst hq2
    have hp2 : p2 ≠ 0 := by
      intro h
      have h1 := (hnp r2 (-r1) (by rw [h]; (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)) (by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)) (by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf))).2
      exact hr1 (neg_eq_zero.mp h1)
    have hr2 : r2 = 0 := by
      have h : p2 * r2 = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * iw
      exact (mul_eq_zero.mp h).resolve_left hp2
    subst hr2
    have hB : r1 ^ 2 * p2 ^ 2 = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 8 : Kf) * Bq
    exact mul_ne_zero (pow_ne_zero 2 hr1) (pow_ne_zero 2 hp2) hB
  · by_cases hp2 : p2 = 0
    · exfalso
      subst hp2
      have hq2 : q2 = 0 := by
        have h : q2 ^ 2 = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) iw
        exact (pow_eq_zero_iff (by norm_num)).mp h
      subst hq2
      have hr2 : r2 ≠ 0 := by
        intro h
        have h1 := (hnp 0 1 (by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)) (by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)) (by rw [h]; (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf))).2
        exact one_ne_zero h1
      have hq1 : q1 = 0 := by
        have h : q1 * r2 ^ 2 = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) T1
        exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hr2)
      subst hq1
      have hr1 : r1 = 0 := by
        have h : p1 * r1 = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * iv
        exact (mul_eq_zero.mp h).resolve_left hp1
      subst hr1
      have hB : p1 ^ 2 * r2 ^ 2 = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 8 : Kf) * Bq
      exact mul_ne_zero (pow_ne_zero 2 hp1) (pow_ne_zero 2 hr2) hB
    · obtain ⟨t, ht⟩ : ∃ t : Kf, q1 = p1 * t :=
        ⟨q1 * p1⁻¹, by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-q1) * mul_inv_cancel₀ hp1⟩
      obtain ⟨u, hu⟩ : ∃ u : Kf, q2 = p2 * u :=
        ⟨q2 * p2⁻¹, by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-q2) * mul_inv_cancel₀ hp2⟩
      subst ht
      subst hu
      have hr1 : r1 = -(p1 * t ^ 2) / 2 := by
        have h : p1 * (2 * r1 + p1 * t ^ 2) = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) iv
        have h' := (mul_eq_zero.mp h).resolve_left hp1
        linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * h'
      have hr2 : r2 = -(p2 * u ^ 2) / 2 := by
        have h : p2 * (2 * r2 + p2 * u ^ 2) = 0 := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) iw
        have h' := (mul_eq_zero.mp h).resolve_left hp2
        linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * h'
      subst hr1
      subst hr2
      have E1 : 2 * u + t + t * u ^ 4 / 4 + t ^ 2 * u ^ 3 / 2 = 0 := by
        have h : p1 * p2 ^ 2 * (2 * u + t + t * u ^ 4 / 4 + t ^ 2 * u ^ 3 / 2) = 0 := by
          linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) T1
        exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hp1 (pow_ne_zero 2 hp2))
      have E2 : 2 * t + u + u * t ^ 4 / 4 + u ^ 2 * t ^ 3 / 2 = 0 := by
        have h : p1 ^ 2 * p2 * (2 * t + u + u * t ^ 4 / 4 + u ^ 2 * t ^ 3 / 2) = 0 := by
          linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) T2
        exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (pow_ne_zero 2 hp1) hp2)
      have BB : 8 * (t - u) ^ 4
          - 24 * ((1 + t ^ 4 / 4) * (1 + u ^ 4 / 4) - 2 * t * u * (t ^ 2 + u ^ 2)) = 0 := by
        have h : p1 ^ 2 * p2 ^ 2 * (8 * (t - u) ^ 4
            - 24 * ((1 + t ^ 4 / 4) * (1 + u ^ 4 / 4) - 2 * t * u * (t ^ 2 + u ^ 2))) = 0 := by
          linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) Bq
        exact (mul_eq_zero.mp h).resolve_left
          (mul_ne_zero (pow_ne_zero 2 hp1) (pow_ne_zero 2 hp2))
      have htu : t ≠ u := by
        intro h
        subst h
        have h1 := (hnp p2 (-p1) (by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)) (by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)) (by (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf))).1
        exact hp2 h1
      obtain ⟨hA, hb⟩ := IIa_tu t u htu E1 E2 BB
      obtain ⟨c, hc⟩ : ∃ c : Kf, c * p2 = -(p1 ^ 2 * t ^ 3) :=
        ⟨-(p1 ^ 2 * t ^ 3) * p2⁻¹, by
          linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-(p1 ^ 2 * t ^ 3)) * mul_inv_cancel₀ hp2⟩
      refine ⟨c, ?_, ?_, ?_⟩
      · linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * hc
      · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (p1 ^ 2 / 4) * hA - u * hc
      · linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-(p1 ^ 2 * t) / 2) * hb + (u ^ 2 / 2) * hc

set_option maxHeartbeats 800000 in
theorem sq_Ps4 (j : Kf) (hj : j * j = -1) (p1 q1 r1 p2 q2 r2 c : Kf)
    (iv : 2 * p1 * r1 + q1 ^ 2 = 0) (h1 : 2 * q1 * r1 = c * p2)
    (h2 : p1 ^ 2 + r1 ^ 2 = c * q2) (h3 : 2 * p1 * q1 = c * r2) :
    (fun i => Ps4 j 0 p1 q1 r1 i * Ps4 j 0 p1 q1 r1 i : (V4 Kf)) = c • Ps4 j 0 p2 q2 r2 := by
  rw [Ps4_mul j hj]
  funext i
  fin_cases i
  · show Ps4 j _ _ _ _ 0 = c * Ps4 j 0 p2 q2 r2 0
    simp only [Ps4_0]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) iv + h1 + h2 + h3
  · show Ps4 j _ _ _ _ 1 = c * Ps4 j 0 p2 q2 r2 1
    simp only [Ps4_1]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) iv + j * h1 - h2 - j * h3
  · show Ps4 j _ _ _ _ 2 = c * Ps4 j 0 p2 q2 r2 2
    simp only [Ps4_2]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) iv - h1 + h2 - h3
  · show Ps4 j _ _ _ _ 3 = c * Ps4 j 0 p2 q2 r2 3
    simp only [Ps4_3]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) iv - j * h1 - h2 + j * h3

set_option maxHeartbeats 800000 in
theorem HypIIa_proof [Fact (∃ i : Kf, i ^ 2 = -1)] : (HypIIa (Kf := Kf)) := by
  unfold HypIIa
  intro v w hv1 hv2 hw1 hw2 hind i1 i2 i3
  have hj : ((Ii (Kf := Kf)) : Kf) * ((Ii (Kf := Kf)) : Kf) = -1 := (Ii_mul_Ii (Kf := Kf))
  obtain ⟨p1, q1, r1, hv⟩ : ∃ p q r : Kf, v = Ps4 ((Ii (Kf := Kf)) : Kf) 0 p q r :=
    ⟨_, _, _, Ps4_param ((Ii (Kf := Kf)) : Kf) hj v hv1⟩
  obtain ⟨p2, q2, r2, hw⟩ : ∃ p q r : Kf, w = Ps4 ((Ii (Kf := Kf)) : Kf) 0 p q r :=
    ⟨_, _, _, Ps4_param ((Ii (Kf := Kf)) : Kf) hj w hw1⟩
  subst hv
  subst hw
  have hvv := Ps4_mul ((Ii (Kf := Kf)) : Kf) hj 0 p1 q1 r1 0 p1 q1 r1
  have hww := Ps4_mul ((Ii (Kf := Kf)) : Kf) hj 0 p2 q2 r2 0 p2 q2 r2
  rw [ip_Ps4 (Ii : Kf) hj] at hv2 hw2
  rw [t3_ip_r, hww, ip_Ps4 (Ii : Kf) hj] at i1
  rw [t3_ip_l, hvv, ip_Ps4 (Ii : Kf) hj] at i2
  simp only [br] at i3
  rw [t4_ip, hvv, hww] at i3
  simp only [ip_Ps4 (Ii : Kf) hj] at i3
  have iv : 2 * p1 * r1 + q1 ^ 2 = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hv2
  have iw : 2 * p2 * r2 + q2 ^ 2 = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hw2
  have T1 : 2 * p1 * p2 * q2 + q1 * (p2 ^ 2 + r2 ^ 2) + 2 * r1 * q2 * r2 = 0 := by
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * i1
  have T2 : 2 * p2 * p1 * q1 + q2 * (p1 ^ 2 + r1 ^ 2) + 2 * r2 * q1 * r1 = 0 := by
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * i2
  have Bq : -24 * (4 * q1 * r1 * p2 * q2 + (p1 ^ 2 + r1 ^ 2) * (p2 ^ 2 + r2 ^ 2)
      + 4 * p1 * q1 * q2 * r2) + 32 * (p1 * r2 + q1 * q2 + r1 * p2) ^ 2 = 0 := by
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) i3 + 8 * (2 * p2 * r2 + q2 ^ 2) * iv
  have hnp : ∀ s t : Kf, s * p1 + t * p2 = 0 → s * q1 + t * q2 = 0 → s * r1 + t * r2 = 0 →
      s = 0 ∧ t = 0 := by
    intro s t h1 h2 h3
    apply hind
    funext i
    fin_cases i
    · show s * Ps4 ((Ii (Kf := Kf)) : Kf) 0 p1 q1 r1 0 + t * Ps4 ((Ii (Kf := Kf)) : Kf) 0 p2 q2 r2 0 = 0
      simp only [Ps4_0]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h1 + h2 + h3
    · show s * Ps4 ((Ii (Kf := Kf)) : Kf) 0 p1 q1 r1 1 + t * Ps4 ((Ii (Kf := Kf)) : Kf) 0 p2 q2 r2 1 = 0
      simp only [Ps4_1]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) ((Ii (Kf := Kf)) : Kf) * h1 - h2 - ((Ii (Kf := Kf)) : Kf) * h3
    · show s * Ps4 ((Ii (Kf := Kf)) : Kf) 0 p1 q1 r1 2 + t * Ps4 ((Ii (Kf := Kf)) : Kf) 0 p2 q2 r2 2 = 0
      simp only [Ps4_2]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * h1 + h2 - h3
    · show s * Ps4 ((Ii (Kf := Kf)) : Kf) 0 p1 q1 r1 3 + t * Ps4 ((Ii (Kf := Kf)) : Kf) 0 p2 q2 r2 3 = 0
      simp only [Ps4_3]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-((Ii (Kf := Kf)) : Kf)) * h1 - h2 + ((Ii (Kf := Kf)) : Kf) * h3
  obtain ⟨c, a1, a2, a3⟩ := IIa_pqr p1 q1 r1 p2 q2 r2 iv iw T1 T2 Bq hnp
  obtain ⟨c', b1, b2, b3⟩ := IIa_pqr p2 q2 r2 p1 q1 r1 iw iv (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) T2)
    (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) T1) (by linear_combination Bq)
    (fun s t h1 h2 h3 => by
      have h := hnp t s (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h1) (by linear_combination h2)
        (by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h3)
      exact ⟨h.2, h.1⟩)
  exact ⟨⟨c, sq_Ps4 ((Ii (Kf := Kf)) : Kf) hj p1 q1 r1 p2 q2 r2 c iv a1 a2 a3⟩,
    ⟨c', sq_Ps4 ((Ii (Kf := Kf)) : Kf) hj p2 q2 r2 p1 q1 r1 c' iw b1 b2 b3⟩⟩

def e2 (d : (V4 Kf)) : Kf := (tau d ^ 2 - ip d d) / 2

end

end PEqualNP.Outside.L_gct_210_aux.FLK

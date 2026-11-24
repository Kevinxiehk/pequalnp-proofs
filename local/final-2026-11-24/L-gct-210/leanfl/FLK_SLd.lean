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

def outer (v : (V4 Kf)) (x : Fin 5 → Kf) : (M45 Kf) := fun p => v p.1 * x p.2

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

theorem t3_ip_l (x y z : (V4 Kf)) : t3 x y z = ip (fun i => x i * y i : (V4 Kf)) z := by
  simp only [t3, ip]

set_option maxHeartbeats 800000 in
theorem t4_ip (x y z w : (V4 Kf)) :
    t4 x y z w = ip (fun i => x i * y i : (V4 Kf)) (fun i => z i * w i : (V4 Kf)) := by
  simp only [t4, ip]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

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

set_option maxHeartbeats 800000 in
theorem vperp_coords (v : (V4 Kf)) (kap : Kf) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0) (x : (V4 Kf)) (hx : tau x = 0)
    (hi : ip x x = 0) (ht : t3 v v x = 0) : ∃ p r : Kf, x = Qv v 0 p 0 r ∧ p * r = 0 := by
  obtain ⟨p, q, r, rfl⟩ := Qv_V v kap hkap hk h1 h2 h3 x hx
  have hvv : (fun i => v i * v i : (V4 Kf)) = Qv v 0 0 1 0 := by
    funext i
    simp only [Qv]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  rw [t3_ip_l, hvv, ip_Qv v kap hk h1 h2 h3] at ht
  have hq : q = 0 := by
    have h : kap * q = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * ht
    exact (mul_eq_zero.mp h).resolve_left hkap
  subst hq
  rw [ip_Qv v kap hk h1 h2 h3] at hi
  have hpr : p * r = 0 := by
    have h : kap * (p * r) = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 8 : Kf) * hi
    exact (mul_eq_zero.mp h).resolve_left hkap
  exact ⟨p, r, rfl, hpr⟩

set_option maxHeartbeats 800000 in
theorem vperp1_coords (v : (V4 Kf)) (kap : Kf) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (h1 : tau v = 0) (h2 : ip v v = 0) (h3 : t3 v v v = 0) (x : (V4 Kf)) (hx : tau x = 0)
    (hi : ip v x = 0) : ∃ p q : Kf, x = Qv v 0 p q 0 := by
  obtain ⟨p, q, r, rfl⟩ := Qv_V v kap hkap hk h1 h2 h3 x hx
  have hv' : v = Qv v 0 1 0 0 := by
    funext i
    simp only [Qv]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  have hi' : ip (Qv v 0 1 0 0) (Qv v 0 p q r) = 0 := by
    rw [← hv']
    exact hi
  rw [ip_Qv v kap hk h1 h2 h3] at hi'
  have hr : r = 0 := by
    have h : kap * r = 0 := by linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * hi'
    exact (mul_eq_zero.mp h).resolve_left hkap
  subst hr
  exact ⟨p, q, rfl⟩

set_option maxHeartbeats 800000 in
theorem br_13 (v : (V4 Kf)) (kap : Kf) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (P1 R1 P2 R2 P3 R3 P4 R4 : Kf) :
    br (Qv v 0 P1 0 R1) (Qv v 0 P2 0 R2) (Qv v 0 P3 0 R3) (Qv v 0 P4 0 R4) =
      -24 * kap * (P1 * P2 * P3 * P4) - 24 * kap ^ 3 * (R1 * R2 * R3 * R4)
      + 8 * kap ^ 2 * (P1 * P2 * R3 * R4 + P1 * P3 * R2 * R4 + P1 * P4 * R2 * R3
        + P2 * P3 * R1 * R4 + P2 * P4 * R1 * R3 + P3 * P4 * R1 * R2) := by
  simp only [br]
  rw [t4_ip, Qv_mul v kap hk, Qv_mul v kap hk]
  simp only [ip_Qv v kap hk h1 h2 h3]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

set_option maxHeartbeats 800000 in
theorem t3_Qv2 (v : (V4 Kf)) (kap : Kf) (hk : ∀ i, v i ^ 4 = kap) (h1 : tau v = 0) (h2 : ip v v = 0)
    (h3 : t3 v v v = 0) (P1 k1 P2 k2 P3 k3 : Kf) :
    t3 (Qv v 0 P1 k1 0) (Qv v 0 P2 k2 0) (Qv v 0 P3 k3 0) =
      4 * kap * (P1 * P2 * k3 + P1 * k2 * P3 + k1 * P2 * P3) := by
  rw [t3_ip_l, Qv_mul v kap hk, ip_Qv v kap hk h1 h2 h3]
  (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)

theorem sw02_1 : sw02 1 = 1 := by decide

theorem sw02_2 : sw02 2 = 0 := by decide

set_option maxHeartbeats 800000 in
theorem S8a (K : Submodule Kf (M45 Kf)) (hK : SLev K)
    (hd : Module.finrank Kf (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)) = 2)
    (Yu : (M45 Kf)) (hYu : Yu ∈ K) (hu0 : (rs (Kf := Kf)) Yu ≠ 0) (huu : ip ((rs (Kf := Kf)) Yu) ((rs (Kf := Kf)) Yu) = 0)
    (v : (V4 Kf)) (hv : v ≠ 0) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (kap : Kf) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap)
    (hform : ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), ∃ x : Fin 5 → Kf,
      Z = outer v x)
    (σ : Equiv.Perm (Fin 5))
    (c3 : ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), col Z (σ 3) = 0)
    (c4 : ∀ Z ∈ (K ⊓ LinearMap.ker (rs (Kf := Kf)) : Submodule Kf (M45 Kf)), col Z (σ 4) = 0)
    (s1 : t3 v v ((rs (Kf := Kf)) Yu) = 0) (s2 : t3 v v ((phi (Kf := Kf)) (σ 3) Yu) = 0)
    (s3 : t3 v v ((phi (Kf := Kf)) (σ 4) Yu) = 0) :
    ∃ pu : Kf, pu ≠ 0 ∧ (∀ i, (rs (Kf := Kf)) Yu i = pu * v i) ∧
      ∀ P0 P1 P2 : Kf, ∃ R ∈ K, (∀ i, R (i, σ 0) = P0 * v i) ∧ (∀ i, R (i, σ 1) = P1 * v i) ∧
        (∀ i, R (i, σ 2) = P2 * v i) ∧ (∀ i, R (i, σ 3) = 0) ∧ (∀ i, R (i, σ 4) = 0) := by
  have hNs := SLev_N K hK
  have hrsN := rs_N K
  have hut : tau ((rs (Kf := Kf)) Yu) = 0 := tau_rs K hK Yu hYu
  obtain ⟨pu, ru, hucoord, hpur⟩ := vperp_coords v kap hkap hk hv1 hv2 hv3 ((rs (Kf := Kf)) Yu) hut huu s1
  have hu_i : ∀ i, (rs (Kf := Kf)) Yu i = pu * v i + ru * v i ^ 3 := by
    intro i
    have h := congrFun hucoord i
    simp only [Qv] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
  obtain ⟨W01, hW01N, a0, a1, a2, a3, a4⟩ := S8_elem _ hNs hrsN hd v hv hform σ c3 c4
  obtain ⟨W21, hW21N, b0, b1, b2, b3, b4⟩ := S8_elem _ hNs hrsN hd v hv hform (σ * sw02)
    (fun Z hZ => by
      rw [Equiv.Perm.mul_apply, sw02_3]
      exact c3 Z hZ)
    (fun Z hZ => by
      rw [Equiv.Perm.mul_apply, sw02_4]
      exact c4 Z hZ)
  rw [Equiv.Perm.mul_apply, sw02_0] at b0
  rw [Equiv.Perm.mul_apply, sw02_1] at b1
  rw [Equiv.Perm.mul_apply, sw02_2] at b2
  rw [Equiv.Perm.mul_apply, sw02_3] at b3
  rw [Equiv.Perm.mul_apply, sw02_4] at b4
  have hW01K : W01 ∈ K := (Submodule.mem_inf.mp hW01N).1
  have hW21K : W21 ∈ K := (Submodule.mem_inf.mp hW21N).1
  have wa0 : ∀ i, W01 (i, σ 0) = v i := fun i => congrFun a0 i
  have wa1 : ∀ i, W01 (i, σ 1) = -1 * v i := fun i => congrFun a1 i
  have wa2 : ∀ i, W01 (i, σ 2) = 0 := fun i => congrFun a2 i
  have wa3 : ∀ i, W01 (i, σ 3) = 0 := fun i => congrFun a3 i
  have wa4 : ∀ i, W01 (i, σ 4) = 0 := fun i => congrFun a4 i
  have wb2 : ∀ i, W21 (i, σ 2) = v i := fun i => congrFun b0 i
  have wb1 : ∀ i, W21 (i, σ 1) = -1 * v i := fun i => congrFun b1 i
  have wb0 : ∀ i, W21 (i, σ 0) = 0 := fun i => congrFun b2 i
  have wb3 : ∀ i, W21 (i, σ 3) = 0 := fun i => congrFun b3 i
  have wb4 : ∀ i, W21 (i, σ 4) = 0 := fun i => congrFun b4 i
  have hne0 : col W01 (σ 0) ≠ 0 := by
    rw [a0]
    exact hv
  have hne1 : col W01 (σ 1) ≠ 0 := by
    rw [a1]
    intro h
    exact hv ((smul_eq_zero.mp h).resolve_left (by norm_num))
  have hne2 : col W21 (σ 2) ≠ 0 := by
    rw [b0]
    exact hv
  obtain ⟨be0, hbe0⟩ := Biii K hK Yu hYu huu W01 hW01N (σ 0) hne0
  obtain ⟨be1', hbe1⟩ := Biii K hK Yu hYu huu W01 hW01N (σ 1) hne1
  obtain ⟨be2, hbe2⟩ := Biii K hK Yu hYu huu W21 hW21N (σ 2) hne2
  rw [a0] at hbe0
  rw [a1] at hbe1
  rw [b0] at hbe2
  obtain ⟨be1, hb1d⟩ : ∃ be1 : Kf, be1 = -be1' := ⟨_, rfl⟩
  have f0 : ∀ i, 2 * Yu (i, σ 0) - (rs (Kf := Kf)) Yu i = be0 * v i := fun i => congrFun hbe0 i
  have f1 : ∀ i, 2 * Yu (i, σ 1) - (rs (Kf := Kf)) Yu i = be1 * v i := by
    intro i
    have h : 2 * Yu (i, σ 1) - (rs (Kf := Kf)) Yu i = be1' * (-1 * v i) := congrFun hbe1 i
    rw [hb1d]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
  have f2 : ∀ i, 2 * Yu (i, σ 2) - (rs (Kf := Kf)) Yu i = be2 * v i := fun i => congrFun hbe2 i
  have hb3i : ip ((phi (Kf := Kf)) (σ 3) Yu) ((phi (Kf := Kf)) (σ 3) Yu) = 0 := by
    rw [ip_phi K hK Yu Yu hYu hYu (σ 3)]
    exact huu
  have hb4i : ip ((phi (Kf := Kf)) (σ 4) Yu) ((phi (Kf := Kf)) (σ 4) Yu) = 0 := by
    rw [ip_phi K hK Yu Yu hYu hYu (σ 4)]
    exact huu
  obtain ⟨pi3, rho3, hb3, hpr3⟩ := vperp_coords v kap hkap hk hv1 hv2 hv3 ((phi (Kf := Kf)) (σ 3) Yu)
    (tau_phi K hK Yu hYu (σ 3)) hb3i s2
  obtain ⟨pi4, rho4, hb4, hpr4⟩ := vperp_coords v kap hkap hk hv1 hv2 hv3 ((phi (Kf := Kf)) (σ 4) Yu)
    (tau_phi K hK Yu hYu (σ 4)) hb4i s3
  have f3 : ∀ i, 2 * Yu (i, σ 3) - (rs (Kf := Kf)) Yu i = pi3 * v i + rho3 * v i ^ 3 := by
    intro i
    have h := congrFun hb3 i
    rw [phi_apply] at h
    simp only [Qv] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
  have f4 : ∀ i, 2 * Yu (i, σ 4) - (rs (Kf := Kf)) Yu i = pi4 * v i + rho4 * v i ^ 3 := by
    intro i
    have h := congrFun hb4 i
    rw [phi_apply] at h
    simp only [Qv] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
  have hsumphi : ∀ i, (be0 + be1 + be2 + pi3 + pi4) * v i + (rho3 + rho4) * v i ^ 3 =
      -3 * pu * v i + -3 * ru * v i ^ 3 := by
    intro i
    have h := congrFun (sum_cols_perm σ Yu) i
    simp only [Pi.add_apply, col] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) 2 * h - 3 * hu_i i - f0 i - f1 i - f2 i - f3 i - f4 i
  have hsumco : be0 + be1 + be2 + pi3 + pi4 = -3 * pu ∧ rho3 + rho4 = -3 * ru := by
    have e : Qv v 0 (be0 + be1 + be2 + pi3 + pi4) 0 (rho3 + rho4) =
        Qv v 0 (-3 * pu) 0 (-3 * ru) := by
      funext i
      simp only [Qv]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hsumphi i
    obtain ⟨_, q1, _, q3⟩ := Qv_inj v kap hkap hk hv1 hv2 hv3 _ _ _ _ _ _ _ _ e
    exact ⟨q1, q3⟩
  have hmemY : ∀ t x0 x2 : Kf, t • Yu + x0 • W01 + x2 • W21 ∈ K := fun t x0 x2 =>
    K.add_mem (K.add_mem (K.smul_mem t hYu) (K.smul_mem x0 hW01K)) (K.smul_mem x2 hW21K)
  have hcol : ∀ t x0 x2 : Kf,
      col ((cperm (Kf := Kf)) σ (t • Yu + x0 • W01 + x2 • W21)) 0 =
        Qv v 0 (t * (be0 + pu) / 2 + x0) 0 (t * ru / 2) ∧
      col ((cperm (Kf := Kf)) σ (t • Yu + x0 • W01 + x2 • W21)) 1 =
        Qv v 0 (t * (be1 + pu) / 2 - x0 - x2) 0 (t * ru / 2) ∧
      col ((cperm (Kf := Kf)) σ (t • Yu + x0 • W01 + x2 • W21)) 2 =
        Qv v 0 (t * (be2 + pu) / 2 + x2) 0 (t * ru / 2) ∧
      col ((cperm (Kf := Kf)) σ (t • Yu + x0 • W01 + x2 • W21)) 3 =
        Qv v 0 (t * (pi3 + pu) / 2) 0 (t * (rho3 + ru) / 2) ∧
      col ((cperm (Kf := Kf)) σ (t • Yu + x0 • W01 + x2 • W21)) 4 =
        Qv v 0 (t * (pi4 + pu) / 2) 0 (t * (rho4 + ru) / 2) := by
    intro t x0 x2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa0, wb0]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (t / 2) * f0 i + (t / 2) * hu_i i
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa1, wb1]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (t / 2) * f1 i + (t / 2) * hu_i i
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa2, wb2]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (t / 2) * f2 i + (t / 2) * hu_i i
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa3, wb3]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (t / 2) * f3 i + (t / 2) * hu_i i
    · funext i
      simp only [col, cperm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Qv, wa4, wb4]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (t / 2) * f4 i + (t / 2) * hu_i i
  have hKσ := SLev_perm σ K hK
  have G4 : ∀ t x0 x2 : Kf,
      br (Qv v 0 (t * (be0 + pu) / 2 + x0) 0 (t * ru / 2))
        (Qv v 0 (t * (be1 + pu) / 2 - x0 - x2) 0 (t * ru / 2))
        (Qv v 0 (t * (be2 + pu) / 2 + x2) 0 (t * ru / 2))
        (Qv v 0 (t * (pi3 + pu) / 2) 0 (t * (rho3 + ru) / 2)) = 0 := by
    intro t x0 x2
    have h := (C34 _ hKσ _ (Submodule.mem_map_of_mem (hmemY t x0 x2)) 4).2.2
    rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2] at h
    obtain ⟨e0, e1, e2, e3, e4⟩ := hcol t x0 x2
    rw [e0, e1, e2, e3] at h
    exact h
  have G3 : ∀ t x0 x2 : Kf,
      br (Qv v 0 (t * (be0 + pu) / 2 + x0) 0 (t * ru / 2))
        (Qv v 0 (t * (be1 + pu) / 2 - x0 - x2) 0 (t * ru / 2))
        (Qv v 0 (t * (be2 + pu) / 2 + x2) 0 (t * ru / 2))
        (Qv v 0 (t * (pi4 + pu) / 2) 0 (t * (rho4 + ru) / 2)) = 0 := by
    intro t x0 x2
    have h := (C34 _ hKσ _ (Submodule.mem_map_of_mem (hmemY t x0 x2)) 3).2.2
    rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2] at h
    obtain ⟨e0, e1, e2, e3, e4⟩ := hcol t x0 x2
    rw [e0, e1, e2, e4] at h
    exact h
  have hp3 : pi3 = -pu := by
    have g1 := G4 1 1 (-2)
    have gm1 := G4 (-1) 1 (-2)
    have g2 := G4 2 1 (-2)
    have gm2 := G4 (-2) 1 (-2)
    rw [br_13 v kap hk hv1 hv2 hv3] at g1 gm1 g2 gm2
    have h : kap * (pi3 + pu) = 0 := by
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 288 : Kf) * (8 * (g1 - gm1) - (g2 - gm2))
    have h' := (mul_eq_zero.mp h).resolve_left hkap
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h'
  have hp4 : pi4 = -pu := by
    have g1 := G3 1 1 (-2)
    have gm1 := G3 (-1) 1 (-2)
    have g2 := G3 2 1 (-2)
    have gm2 := G3 (-2) 1 (-2)
    rw [br_13 v kap hk hv1 hv2 hv3] at g1 gm1 g2 gm2
    have h : kap * (pi4 + pu) = 0 := by
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 288 : Kf) * (8 * (g1 - gm1) - (g2 - gm2))
    have h' := (mul_eq_zero.mp h).resolve_left hkap
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h'
  subst hp3
  subst hp4
  have hr3 : ru * (rho3 + ru) = 0 := by
    have g1 := G4 1 1 (-2)
    have gm1 := G4 (-1) 1 (-2)
    have g2 := G4 2 1 (-2)
    have gm2 := G4 (-2) 1 (-2)
    rw [br_13 v kap hk hv1 hv2 hv3] at g1 gm1 g2 gm2
    have h : kap ^ 2 * (ru * (rho3 + ru)) = 0 := by
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 144 : Kf) * (16 * (g1 + gm1) - (g2 + gm2))
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hkap)
  have hr4 : ru * (rho4 + ru) = 0 := by
    have g1 := G3 1 1 (-2)
    have gm1 := G3 (-1) 1 (-2)
    have g2 := G3 2 1 (-2)
    have gm2 := G3 (-2) 1 (-2)
    rw [br_13 v kap hk hv1 hv2 hv3] at g1 gm1 g2 gm2
    have h : kap ^ 2 * (ru * (rho4 + ru)) = 0 := by
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 144 : Kf) * (16 * (g1 + gm1) - (g2 + gm2))
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hkap)
  by_cases hru : ru = 0
  · subst hru
    have hpu : pu ≠ 0 := by
      intro h
      apply hu0
      funext i
      rw [hu_i i, h]
      simp
    have h3r : rho3 = 0 := (mul_eq_zero.mp hpr3).resolve_left (neg_ne_zero.mpr hpu)
    have h4r : rho4 = 0 := (mul_eq_zero.mp hpr4).resolve_left (neg_ne_zero.mpr hpu)
    subst h3r
    subst h4r
    have hbsum : be0 + be1 + be2 = -pu := by linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hsumco.1
    have hinv := mul_inv_cancel₀ hpu
    refine ⟨pu, hpu, fun i => by rw [hu_i i]; (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf), ?_⟩
    intro P0 P1 P2
    refine ⟨((P0 + P1 + P2) * pu⁻¹) • Yu
      + (P0 - (P0 + P1 + P2) * pu⁻¹ * ((be0 + pu) / 2)) • W01
      + (P2 - (P0 + P1 + P2) * pu⁻¹ * ((be2 + pu) / 2)) • W21, hmemY _ _ _, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa0, wb0]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) ((P0 + P1 + P2) * pu⁻¹ / 2) * f0 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa1, wb1]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) ((P0 + P1 + P2) * pu⁻¹ / 2) * f1 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
        + ((P0 + P1 + P2) * pu⁻¹ / 2 * v i) * hbsum + ((P0 + P1 + P2) * v i) * hinv
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa2, wb2]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) ((P0 + P1 + P2) * pu⁻¹ / 2) * f2 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa3, wb3]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) ((P0 + P1 + P2) * pu⁻¹ / 2) * f3 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wa4, wb4]
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) ((P0 + P1 + P2) * pu⁻¹ / 2) * f4 i
        + ((P0 + P1 + P2) * pu⁻¹ / 2) * hu_i i
  · exfalso
    have h3' : rho3 + ru = 0 := (mul_eq_zero.mp hr3).resolve_left hru
    have h4' : rho4 + ru = 0 := (mul_eq_zero.mp hr4).resolve_left hru
    apply hru
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) hsumco.2 - h3' - h4'

set_option maxHeartbeats 800000 in
theorem S8b (K : Submodule Kf (M45 Kf)) (hK : SLev K) (hq : Module.finrank Kf (K.map (rs (Kf := Kf))) = 2)
    (Yu : (M45 Kf)) (hYu : Yu ∈ K) (huperp : ∀ s ∈ K.map (rs (Kf := Kf)), ip ((rs (Kf := Kf)) Yu) s = 0)
    (v : (V4 Kf)) (hv1 : tau v = 0) (hv2 : ip v v = 0) (hv3 : t3 v v v = 0)
    (kap : Kf) (hkap : kap ≠ 0) (hk : ∀ i, v i ^ 4 = kap) (σ : Equiv.Perm (Fin 5))
    (pu : Kf) (hpu : pu ≠ 0) (hu_i : ∀ i, (rs (Kf := Kf)) Yu i = pu * v i)
    (hrel : ∀ P0 P1 P2 : Kf, ∃ R ∈ K, (∀ i, R (i, σ 0) = P0 * v i) ∧
      (∀ i, R (i, σ 1) = P1 * v i) ∧ (∀ i, R (i, σ 2) = P2 * v i) ∧
      (∀ i, R (i, σ 3) = 0) ∧ (∀ i, R (i, σ 4) = 0)) : False := by
  have hv0 : v 0 ≠ 0 := by
    intro h0
    apply hkap
    rw [← hk 0, h0]
    norm_num
  have hu0 : (rs (Kf := Kf)) Yu ≠ 0 := by
    intro h
    have e := hu_i 0
    rw [h] at e
    exact (mul_ne_zero hpu hv0) e.symm
  obtain ⟨Y4, hY4, hY4n⟩ : ∃ Y4 ∈ K, ∀ c : Kf, (rs (Kf := Kf)) Y4 ≠ c • (rs (Kf := Kf)) Yu := by
    by_contra hcon
    have hall : ∀ Y ∈ K, ∃ c : Kf, (rs (Kf := Kf)) Y = c • (rs (Kf := Kf)) Yu := by
      intro Y hY
      by_contra h
      exact hcon ⟨Y, hY, fun c hc => h ⟨c, hc⟩⟩
    have hle : K.map (rs (Kf := Kf)) ≤ Submodule.span Kf {(rs (Kf := Kf)) Yu} := by
      rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨c, hc⟩ := hall Y hY
      rw [hc]
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu0] at h1
    omega
  have hvs : ip v ((rs (Kf := Kf)) Y4) = 0 := by
    have h := huperp _ (Submodule.mem_map_of_mem hY4)
    simp only [ip] at h ⊢
    have h' : pu * (v 0 * (rs (Kf := Kf)) Y4 0 + v 1 * (rs (Kf := Kf)) Y4 1 + v 2 * (rs (Kf := Kf)) Y4 2 + v 3 * (rs (Kf := Kf)) Y4 3) = 0 := by
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h - (rs (Kf := Kf)) Y4 0 * hu_i 0 - (rs (Kf := Kf)) Y4 1 * hu_i 1 - (rs (Kf := Kf)) Y4 2 * hu_i 2
        - (rs (Kf := Kf)) Y4 3 * hu_i 3
    exact (mul_eq_zero.mp h').resolve_left hpu
  obtain ⟨Ra, hRa, ra0, ra1, ra2, ra3, ra4⟩ := hrel 1 (-1) 0
  obtain ⟨Rb, hRb, rb0, rb1, rb2, rb3, rb4⟩ := hrel 0 (-1) 1
  obtain ⟨Rc, hRc, rc0, rc1, rc2, rc3, rc4⟩ := hrel 1 0 0
  have hrsRa : (rs (Kf := Kf)) Ra = 0 := by
    rw [← sum_cols_perm σ Ra]
    funext i
    simp only [Pi.add_apply, col, ra0, ra1, ra2, ra3, ra4, Pi.zero_apply]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  have hrsRb : (rs (Kf := Kf)) Rb = 0 := by
    rw [← sum_cols_perm σ Rb]
    funext i
    simp only [Pi.add_apply, col, rb0, rb1, rb2, rb3, rb4, Pi.zero_apply]
    (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
  have hrsRc : ∀ i, (rs (Kf := Kf)) Rc i = v i := by
    intro i
    have h := congrFun (sum_cols_perm σ Rc) i
    simp only [Pi.add_apply, col, rc0, rc1, rc2, rc3, rc4] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * h
  have hvsU := hvs
  simp only [ip] at hvsU
  have o0 : ip v (col Y4 (σ 0)) = 0 := by
    have e := ip_col_phi K hK Ra Y4 hRa hY4 hrsRa (σ 0)
    simp only [ip, col, phi_apply, ra0] at e
    simp only [ip, col]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * e + (1 / 2 : Kf) * hvsU
  have o1 : ip v (col Y4 (σ 1)) = 0 := by
    have e := ip_col_phi K hK Ra Y4 hRa hY4 hrsRa (σ 1)
    simp only [ip, col, phi_apply, ra1] at e
    simp only [ip, col]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (-1 / 2 : Kf) * e + (1 / 2 : Kf) * hvsU
  have o2 : ip v (col Y4 (σ 2)) = 0 := by
    have e := ip_col_phi K hK Rb Y4 hRb hY4 hrsRb (σ 2)
    simp only [ip, col, phi_apply, rb2] at e
    simp only [ip, col]
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * e + (1 / 2 : Kf) * hvsU
  have o3 : ip v (col Y4 (σ 3)) = 0 := by
    have e := C2pol K hK Y4 Rc hY4 hRc (σ 3)
    simp only [ip, col, rc3, hrsRc] at e
    simp only [ip, col]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * e
  have o4 : ip v (col Y4 (σ 4)) = 0 := by
    have e := C2pol K hK Y4 Rc hY4 hRc (σ 4)
    simp only [ip, col, rc4, hrsRc] at e
    simp only [ip, col]
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * e
  obtain ⟨pe0, ke0, he0⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 0))
    (C1 K hK Y4 hY4 (σ 0)) o0
  obtain ⟨pe1, ke1, he1⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 1))
    (C1 K hK Y4 hY4 (σ 1)) o1
  obtain ⟨pe2, ke2, he2⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 2))
    (C1 K hK Y4 hY4 (σ 2)) o2
  obtain ⟨pe3, ke3, he3⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 3))
    (C1 K hK Y4 hY4 (σ 3)) o3
  obtain ⟨pe4, ke4, he4⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 (col Y4 (σ 4))
    (C1 K hK Y4 hY4 (σ 4)) o4
  obtain ⟨ps, qs, hs4⟩ := vperp1_coords v kap hkap hk hv1 hv2 hv3 ((rs (Kf := Kf)) Y4)
    (tau_rs K hK Y4 hY4) hvs
  have y40 : ∀ i, Y4 (i, σ 0) = pe0 * v i + ke0 * v i ^ 2 := by
    intro i
    have h := congrFun he0 i
    simp only [Qv, col] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
  have y41 : ∀ i, Y4 (i, σ 1) = pe1 * v i + ke1 * v i ^ 2 := by
    intro i
    have h := congrFun he1 i
    simp only [Qv, col] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
  have y42 : ∀ i, Y4 (i, σ 2) = pe2 * v i + ke2 * v i ^ 2 := by
    intro i
    have h := congrFun he2 i
    simp only [Qv, col] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
  have y43 : ∀ i, Y4 (i, σ 3) = pe3 * v i + ke3 * v i ^ 2 := by
    intro i
    have h := congrFun he3 i
    simp only [Qv, col] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
  have y44 : ∀ i, Y4 (i, σ 4) = pe4 * v i + ke4 * v i ^ 2 := by
    intro i
    have h := congrFun he4 i
    simp only [Qv, col] at h
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) h
  have hksum : ke0 + ke1 + ke2 + ke3 + ke4 = qs := by
    have e : Qv v 0 (pe0 + pe1 + pe2 + pe3 + pe4) (ke0 + ke1 + ke2 + ke3 + ke4) 0 =
        Qv v 0 ps qs 0 := by
      rw [← hs4, ← sum_cols_perm σ Y4, he0, he1, he2, he3, he4]
      funext i
      simp only [Qv, Pi.add_apply]
      (first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring_nf)
    exact (Qv_inj v kap hkap hk hv1 hv2 hv3 _ _ _ _ _ _ _ _ e).2.2.1
  have hqs : qs ≠ 0 := by
    intro h
    apply hY4n (ps * pu⁻¹)
    funext i
    have e := congrFun hs4 i
    simp only [Qv] at e
    rw [e, h]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu_i i]
    have hinv := mul_inv_cancel₀ hpu
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-(ps * v i)) * hinv
  have hc2 : ke3 ^ 2 = qs * ke3 := by
    have e := C2 K hK Y4 hY4 (σ 3)
    rw [he3, hs4, ip_Qv v kap hk hv1 hv2 hv3, ip_Qv v kap hk hv1 hv2 hv3] at e
    apply mul_left_cancel₀ hkap
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * e
  have hKσ := SLev_perm σ K hK
  have TT : ∀ P0 P1 P2 : Kf,
      (t3 (Qv v 0 P0 ke0 0) (Qv v 0 P1 ke1 0) (Qv v 0 P2 ke2 0)
        + t3 (Qv v 0 P0 ke0 0) (Qv v 0 P1 ke1 0) (Qv v 0 pe3 ke3 0)
        + t3 (Qv v 0 P0 ke0 0) (Qv v 0 P2 ke2 0) (Qv v 0 pe3 ke3 0)
        + t3 (Qv v 0 P1 ke1 0) (Qv v 0 P2 ke2 0) (Qv v 0 pe3 ke3 0) = 0) ∧
      (t3 (Qv v 0 P0 ke0 0) (Qv v 0 P1 ke1 0) (Qv v 0 P2 ke2 0)
        + t3 (Qv v 0 P0 ke0 0) (Qv v 0 P1 ke1 0) (Qv v 0 pe4 ke4 0)
        + t3 (Qv v 0 P0 ke0 0) (Qv v 0 P2 ke2 0) (Qv v 0 pe4 ke4 0)
        + t3 (Qv v 0 P1 ke1 0) (Qv v 0 P2 ke2 0) (Qv v 0 pe4 ke4 0) = 0) := by
    intro P0 P1 P2
    obtain ⟨R, hR, r0, r1, r2, r3, r4⟩ := hrel (P0 - pe0) (P1 - pe1) (P2 - pe2)
    have hmem : (cperm (Kf := Kf)) σ (Y4 + R) ∈ K.map ((cperm (Kf := Kf)) σ) :=
      Submodule.mem_map_of_mem (K.add_mem hY4 hR)
    have d0 : col ((cperm (Kf := Kf)) σ (Y4 + R)) 0 = Qv v 0 P0 ke0 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r0]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) y40 i
    have d1 : col ((cperm (Kf := Kf)) σ (Y4 + R)) 1 = Qv v 0 P1 ke1 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r1]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) y41 i
    have d2 : col ((cperm (Kf := Kf)) σ (Y4 + R)) 2 = Qv v 0 P2 ke2 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r2]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) y42 i
    have d3 : col ((cperm (Kf := Kf)) σ (Y4 + R)) 3 = Qv v 0 pe3 ke3 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r3]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) y43 i
    have d4 : col ((cperm (Kf := Kf)) σ (Y4 + R)) 4 = Qv v 0 pe4 ke4 0 := by
      funext i
      simp only [col, cperm_apply, Pi.add_apply, Qv, r4]
      linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) y44 i
    have h4 := (C34 _ hKσ _ hmem 4).2.1
    have h3 := (C34 _ hKσ _ hmem 3).2.1
    rw [sa4.1, sa4.2.1, sa4.2.2.1, sa4.2.2.2, d0, d1, d2, d3] at h4
    rw [sa3.1, sa3.2.1, sa3.2.2.1, sa3.2.2.2, d0, d1, d2, d4] at h3
    exact ⟨h4, h3⟩
  have t000 := TT 0 0 0
  have t010 := TT 0 1 0
  have t001 := TT 0 0 1
  have t011 := TT 0 1 1
  have t100 := TT 1 0 0
  have t101 := TT 1 0 1
  have t110 := TT 1 1 0
  simp only [t3_Qv2 v kap hk hv1 hv2 hv3] at t000 t010 t001 t011 t100 t101 t110
  have e03 : ke0 + ke3 = 0 := by
    apply mul_left_cancel₀ hkap
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (t011.1 - t010.1 - t001.1 + t000.1)
  have e13 : ke1 + ke3 = 0 := by
    apply mul_left_cancel₀ hkap
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (t101.1 - t100.1 - t001.1 + t000.1)
  have e23 : ke2 + ke3 = 0 := by
    apply mul_left_cancel₀ hkap
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (t110.1 - t100.1 - t010.1 + t000.1)
  have e04 : ke0 + ke4 = 0 := by
    apply mul_left_cancel₀ hkap
    linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 4 : Kf) * (t011.2 - t010.2 - t001.2 + t000.2)
  have hk3 : ke3 = 0 := by
    have h : ke3 ^ 2 = 0 := by
      linear_combination (norm := first | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs]) | ring1) (1 / 2 : Kf) * hc2 - (ke3 / 2) * hksum + (ke3 / 2) * (e13 + e23 + e04)
    exact (pow_eq_zero_iff (by norm_num)).mp h
  apply hqs
  linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) (-1 : Kf) * hksum + e13 + e23 + e04 - hk3

set_option maxHeartbeats 800000 in
theorem HypS8_proof : (HypS8 (Kf := Kf)) := by
  unfold HypS8
  intro K hK hq hd Yu hYu hu0 huperp v hv hv1 hv2 hv3 hform σ c3 c4 s1 s2 s3
  obtain ⟨k0, k1, k2, k3⟩ := pow4_iso v hv1 hv2 hv3
  have hkap : t4 v v v v / 4 ≠ 0 := by
    intro h
    apply hv
    apply iso34 v hv1 hv2 hv3
    linear_combination (norm := first | ring1 | field (disch := first | assumption | simp only [nzs, ne_eq, not_false_eq_true] | norm_num [nzs])) 4 * h
  have hk : ∀ i, v i ^ 4 = t4 v v v v / 4 := by
    intro i
    fin_cases i
    · exact k0
    · exact k1
    · exact k2
    · exact k3
  have huu : ip ((rs (Kf := Kf)) Yu) ((rs (Kf := Kf)) Yu) = 0 := huperp _ (Submodule.mem_map_of_mem hYu)
  obtain ⟨pu, hpu, hu_i, hrel⟩ := S8a K hK hd Yu hYu hu0 huu v hv hv1 hv2 hv3 _ hkap hk hform
    σ c3 c4 s1 s2 s3
  exact S8b K hK hq Yu hYu huperp v hv1 hv2 hv3 _ hkap hk σ pu hpu hu_i hrel


def r3 [Fact (∃ i : Kf, i ^ 2 = -1)] : Fin 3 → Kf := ![((Ii (Kf := Kf)) : Kf), -1, -((Ii (Kf := Kf)) : Kf)]

def e2 (d : (V4 Kf)) : Kf := (tau d ^ 2 - ip d d) / 2

end

end PEqualNP.Outside.L_gct_210_aux.FLK

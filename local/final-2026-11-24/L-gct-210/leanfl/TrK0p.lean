import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_210_aux.FLK

open Finset

noncomputable section

set_option profiler true

set_option profiler.threshold 300

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

def HypIIa : Prop :=
  ∀ v w : (V4 Kf), tau v = 0 → ip v v = 0 → tau w = 0 → ip w w = 0 → indep v w →
    t3 v w w = 0 → t3 v v w = 0 → br v v w w = 0 →
    (∃ c : Kf, (fun i => v i * v i : (V4 Kf)) = c • w) ∧ (∃ c : Kf, (fun i => w i * w i : (V4 Kf)) = c • v)

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


def r3 [Fact (∃ i : Kf, i ^ 2 = -1)] : Fin 3 → Kf := ![((Ii (Kf := Kf)) : Kf), -1, -((Ii (Kf := Kf)) : Kf)]

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

theorem Vp_finrank (i : Fin 4) :
    Module.finrank Kf ((sumZero (Kf := Kf)) 4 ⊓ LinearMap.ker (LinearMap.proj i : (V4 Kf) →ₗ[Kf] Kf) :
      Submodule Kf (V4 Kf)) ≤ 2 := by
  have rn := rank_nullity ((sumZero (Kf := Kf)) 4) (LinearMap.proj i : (V4 Kf) →ₗ[Kf] Kf)
  have h3 : Module.finrank Kf ((sumZero (Kf := Kf)) 4) ≤ 3 :=
    (finrank_sumZero (Kf := Kf) (n := 4) (by norm_num)).trans (by norm_num)
  have hne : Module.finrank Kf (((sumZero (Kf := Kf)) 4).map (LinearMap.proj i : (V4 Kf) →ₗ[Kf] Kf)) ≠ 0 := by
    intro h0
    have hb := Submodule.finrank_eq_zero.mp h0
    have hx : (fun a : Fin 4 => (if a = i then (4 : Kf) else 0) - 1) ∈ (sumZero (Kf := Kf)) 4 := by
      rw [mem_sumZero]
      norm_num [Finset.sum_sub_distrib]
    have hm : (LinearMap.proj i : (V4 Kf) →ₗ[Kf] Kf) (fun a : Fin 4 => (if a = i then (4 : Kf) else 0) - 1)
        ∈ ((sumZero (Kf := Kf)) 4).map (LinearMap.proj i : (V4 Kf) →ₗ[Kf] Kf) := Submodule.mem_map_of_mem hx
    rw [hb, Submodule.mem_bot] at hm
    norm_num at hm
  have h4 : Module.finrank Kf ((sumZero (Kf := Kf)) 4 ⊓ LinearMap.ker (LinearMap.proj i : (V4 Kf) →ₗ[Kf] Kf) :
      Submodule Kf (V4 Kf)) + Module.finrank Kf (((sumZero (Kf := Kf)) 4).map (LinearMap.proj i : (V4 Kf) →ₗ[Kf] Kf)) ≤ 3 := by
    rw [← rn]
    exact h3
  omega

theorem inj_succ5 : Function.Injective (fun k : Fin 5 => ((k : ℕ) : Kf) + 1) := by
  intro i j h
  have h' : ((i : ℕ) : Kf) = ((j : ℕ) : Kf) := add_right_cancel h
  exact Fin.ext (cast_inj5 _ _ i.isLt j.isLt h')

def e2 (d : (V4 Kf)) : Kf := (tau d ^ 2 - ip d d) / 2

end

end PEqualNP.Outside.L_gct_210_aux.FLK

import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_1182_aux

open Finset

def enc {m : ℕ} (x : Finset (Fin m)) (b : Bool) : Finset (Option (Fin m)) :=
  let old := x.image (fun i => (some i : Option (Fin m)))
  if b then insert none old else old

def dec {m : ℕ} (c : Finset (Option (Fin m))) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => some i ∈ c)

theorem mem_enc_none {m : ℕ} (x : Finset (Fin m)) (b : Bool) :
    (none ∈ enc x b) ↔ b = true := by
  cases b <;> simp [enc]

theorem mem_enc_some {m : ℕ} (x : Finset (Fin m)) (b : Bool) (i : Fin m) :
    (some i ∈ enc x b) ↔ i ∈ x := by
  cases b <;> simp [enc]

theorem enc_dec {m : ℕ} (c : Finset (Option (Fin m))) : enc (dec c) (decide (none ∈ c)) = c := by
  ext o
  cases o with
  | none => simp [mem_enc_none]
  | some i => simp [mem_enc_some, dec]

theorem dec_enc {m : ℕ} (x : Finset (Fin m)) (b : Bool) : dec (enc x b) = x := by
  ext i; simp [dec, mem_enc_some]

theorem enc_inj {m : ℕ} {x y : Finset (Fin m)} {b c : Bool} (hh : enc x b = enc y c) :
    x = y ∧ b = c := by
  constructor
  · rw [← dec_enc x b, hh, dec_enc]
  · have h1 := mem_enc_none x b
    rw [hh, mem_enc_none] at h1
    cases b <;> cases c <;> simp_all

theorem card_enc {m : ℕ} (x : Finset (Fin m)) (b : Bool) :
    (enc x b).card = x.card + (if b then 1 else 0) := by
  have hi : (x.image (fun i => (some i : Option (Fin m)))).card = x.card :=
    card_image_of_injective _ (Option.some_injective _)
  cases b
  · simp only [enc]
    simpa using hi
  · simp only [enc, if_true]
    rw [card_insert_of_notMem (by simp), hi]

theorem card_dec {m : ℕ} (c : Finset (Option (Fin m))) :
    c.card = (dec c).card + (if none ∈ c then 1 else 0) := by
  have := card_enc (dec c) (decide (none ∈ c))
  rw [enc_dec] at this
  rw [this]
  simp

def scopes (m h : ℕ) : Finset (Finset (Option (Fin m))) :=
  (Finset.univ : Finset (Option (Fin m))).powersetCard (h + 1)

def small (m h : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter (fun x => x.card < h)

def shell (m h : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter (fun x => x.card = h)

def region (m h : ℕ) (s : Finset (Option (Fin m)) → Finset (Option (Fin m))) :
    Finset (Finset (Fin m) × Bool) :=
  (Finset.univ : Finset (Finset (Fin m) × Bool)).filter (fun xb =>
    ∀ E ∈ scopes m h, enc xb.1 xb.2 ∩ E ≠ s E ∩ E)

def allRegions (m h : ℕ) : Finset (Finset (Finset (Fin m) × Bool)) :=
  (Finset.univ : Finset (Finset (Option (Fin m)) → Finset (Option (Fin m)))).image (region m h)

def family (m h : ℕ) : Finset (Finset (Finset (Fin m) × Bool)) :=
  (allRegions m h).filter (fun R =>
    R.image Prod.fst = small m h ∪ shell m h ∧ ∀ x ∈ small m h, (x, false) ∈ R ∧ (x, true) ∈ R)

def lift (m h : ℕ) (F : Finset (Finset (Fin m))) : Finset (Finset (Fin m) × Bool) :=
  (Finset.univ : Finset (Finset (Fin m) × Bool)).filter (fun xb =>
    xb.1 ∈ small m h ∨ (xb.1 ∈ shell m h ∧ xb.2 = decide (xb.1 ∈ F)))

theorem mem_small {m h : ℕ} {x : Finset (Fin m)} : x ∈ small m h ↔ x.card < h := by
  simp [small]

theorem mem_shell {m h : ℕ} {x : Finset (Fin m)} : x ∈ shell m h ↔ x.card = h := by
  simp [shell]

theorem mem_scopes {m h : ℕ} {E : Finset (Option (Fin m))} : E ∈ scopes m h ↔ E.card = h + 1 := by
  simp [scopes, mem_powersetCard]

theorem mem_region {m h : ℕ} {s : Finset (Option (Fin m)) → Finset (Option (Fin m))}
    {xb : Finset (Fin m) × Bool} :
    xb ∈ region m h s ↔ ∀ E ∈ scopes m h, enc xb.1 xb.2 ∩ E ≠ s E ∩ E := by
  simp only [region, mem_filter, mem_univ, true_and]

theorem mem_lift {m h : ℕ} {F : Finset (Finset (Fin m))} {xb : Finset (Fin m) × Bool} :
    xb ∈ lift m h F ↔ xb.1 ∈ small m h ∨ (xb.1 ∈ shell m h ∧ xb.2 = decide (xb.1 ∈ F)) := by
  simp only [lift, mem_filter, mem_univ, true_and]

theorem disj_small_shell {m h : ℕ} {x : Finset (Fin m)} (h1 : x ∈ small m h)
    (h2 : x ∈ shell m h) : False := by
  rw [mem_small] at h1; rw [mem_shell] at h2; omega

theorem lift_eq {m h : ℕ} (F : Finset (Finset (Fin m))) :
    lift m h F = (small m h ×ˢ (univ : Finset Bool)) ∪
      (shell m h).image (fun x => (x, decide (x ∈ F))) := by
  ext ⟨x, b⟩
  simp only [mem_lift, mem_union, mem_product, mem_univ, and_true, mem_image, Prod.mk.injEq]
  constructor
  · rintro (hs | ⟨hs, hb⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨x, hs, rfl, hb.symm⟩
  · rintro (hs | ⟨y, hy, rfl, hb⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨hy, hb.symm⟩

theorem card_lift {m h : ℕ} (F : Finset (Finset (Fin m))) :
    (lift m h F).card = 2 * (small m h).card + (shell m h).card := by
  rw [lift_eq, card_union_of_disjoint, card_product, card_univ, Fintype.card_bool,
    card_image_of_injective]
  · ring
  · intro a b hab
    exact congrArg Prod.fst hab
  · rw [disjoint_left]
    rintro ⟨x, b⟩ h1 h2
    simp only [mem_product] at h1
    simp only [mem_image, Prod.mk.injEq] at h2
    obtain ⟨y, hy, rfl, _⟩ := h2
    exact disj_small_shell h1.1 hy

theorem true_count {m h : ℕ} (F : Finset (Finset (Fin m))) (hF : F ⊆ shell m h) :
    ((lift m h F).filter (fun xb => xb.2 = true)).card = (small m h).card + F.card := by
  have heq : (lift m h F).filter (fun xb => xb.2 = true) =
      (small m h ∪ F).image (fun x => (x, true)) := by
    ext ⟨x, b⟩
    simp only [mem_filter, mem_lift, mem_image, mem_union, Prod.mk.injEq]
    constructor
    · rintro ⟨hs | ⟨hs, hb⟩, rfl⟩
      · exact ⟨x, Or.inl hs, rfl, rfl⟩
      · refine ⟨x, Or.inr ?_, rfl, rfl⟩
        simpa using hb.symm
    · rintro ⟨y, hy, rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr ⟨hF hy, by simp [hy]⟩
  rw [heq, card_image_of_injective _ (fun a b hab => congrArg Prod.fst hab),
    card_union_of_disjoint]
  rw [disjoint_left]
  intro x h1 h2
  exact disj_small_shell h1 (hF h2)

def sF {m : ℕ} (F : Finset (Finset (Fin m))) (E : Finset (Option (Fin m))) :
    Finset (Option (Fin m)) :=
  if none ∈ E ∧ dec E ∈ F then E.erase none else E

theorem sF_inter {m : ℕ} (F : Finset (Finset (Fin m))) (E : Finset (Option (Fin m))) :
    sF F E ∩ E = sF F E := by
  unfold sF
  split_ifs
  · exact inter_eq_left.2 (erase_subset _ _)
  · exact inter_self _

theorem region_sF {m h : ℕ} (F : Finset (Finset (Fin m))) : region m h (sF F) = lift m h F := by
  ext ⟨x, b⟩
  simp only [mem_region, mem_lift, sF_inter]
  constructor
  · intro H
    rcases lt_trichotomy x.card h with hlt | heq | hgt
    · exact Or.inl (mem_small.2 hlt)
    · right
      refine ⟨mem_shell.2 heq, ?_⟩
      have hE : enc x true ∈ scopes m h := by
        rw [mem_scopes, card_enc, heq]; simp
      have H1 := H _ hE
      have hsub : enc x b ∩ enc x true = enc x b := by
        apply inter_eq_left.2
        intro o ho
        cases o with
        | none => simp [mem_enc_none]
        | some i => rw [mem_enc_some] at ho ⊢; exact ho
      rw [hsub] at H1
      have hn : none ∈ enc x true := by simp [mem_enc_none]
      have hd : dec (enc x true) = x := dec_enc x true
      by_cases hxF : x ∈ F
      · have h2 : sF F (enc x true) = enc x false := by
          rw [sF, if_pos ⟨hn, by rw [hd]; exact hxF⟩]
          ext o
          cases o with
          | none => simp [mem_enc_none]
          | some i => simp [mem_enc_some]
        rw [h2] at H1
        cases b
        · exact absurd rfl H1
        · simp [hxF]
      · have h2 : sF F (enc x true) = enc x true := by
          rw [sF, if_neg]
          rintro ⟨_, h3⟩
          exact hxF (hd ▸ h3)
        rw [h2] at H1
        cases b
        · simp [hxF]
        · exact absurd rfl H1
    · exfalso
      obtain ⟨E0, hE0, hcard⟩ := exists_subset_card_eq (show h + 1 ≤ x.card by omega)
      have hE : enc E0 false ∈ scopes m h := by
        rw [mem_scopes, card_enc, hcard]; simp
      have H1 := H _ hE
      have hs : sF F (enc E0 false) = enc E0 false := by
        rw [sF, if_neg]
        rintro ⟨h1, _⟩
        simp [mem_enc_none] at h1
      rw [hs] at H1
      apply H1
      apply inter_eq_right.2
      intro o ho
      cases o with
      | none => simp [mem_enc_none] at ho
      | some i => rw [mem_enc_some] at ho ⊢; exact hE0 ho
  · intro H E hE heq
    rw [mem_scopes] at hE
    by_cases hc : none ∈ E ∧ dec E ∈ F
    · rw [sF, if_pos hc] at heq
      have hb : b = false := by
        have h1 : none ∉ enc x b ∩ E := by rw [heq]; simp
        rw [mem_inter, mem_enc_none] at h1
        cases b
        · rfl
        · exact absurd ⟨rfl, hc.1⟩ h1
      have hsub : dec E ⊆ x := by
        intro i hi
        have h1 : some i ∈ E.erase none := by
          rw [mem_erase]
          exact ⟨by simp, by simpa [dec] using hi⟩
        rw [← heq, mem_inter, mem_enc_some] at h1
        exact h1.1
      have hcd : (dec E).card = h := by
        have := card_dec E
        rw [if_pos hc.1] at this
        omega
      rcases H with hs | ⟨hs, hbF⟩
      · rw [mem_small] at hs
        have := card_le_card hsub
        omega
      · rw [mem_shell] at hs
        have hx : dec E = x := eq_of_subset_of_card_le hsub (by omega)
        rw [hx] at hc
        rw [hb, decide_eq_true hc.2] at hbF
        exact absurd hbF (by decide)
    · rw [sF, if_neg hc] at heq
      have hsub : E ⊆ enc x b := inter_eq_right.1 heq
      have hc1 := card_le_card hsub
      rw [card_enc, hE] at hc1
      rcases H with hs | ⟨hs, hbF⟩
      · rw [mem_small] at hs
        cases b <;> simp at hc1 <;> omega
      · rw [mem_shell] at hs
        cases b
        · simp at hc1
          omega
        · have hEq : E = enc x true :=
            eq_of_subset_of_card_le hsub (by rw [card_enc, hE, hs]; simp)
          apply hc
          rw [hEq, dec_enc]
          refine ⟨by simp [mem_enc_none], ?_⟩
          simpa using hbF.symm

theorem lift_mem_family {m h : ℕ} (F : Finset (Finset (Fin m))) : lift m h F ∈ family m h := by
  rw [family, mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · rw [allRegions, mem_image]
    exact ⟨sF F, mem_univ _, region_sF F⟩
  · ext x
    rw [mem_image, mem_union]
    constructor
    · rintro ⟨⟨y, b⟩, hy, rfl⟩
      rw [mem_lift] at hy
      rcases hy with hs | ⟨hs, _⟩
      · exact Or.inl hs
      · exact Or.inr hs
    · rintro (hs | hs)
      · exact ⟨(x, false), mem_lift.2 (Or.inl hs), rfl⟩
      · exact ⟨(x, decide (x ∈ F)), mem_lift.2 (Or.inr ⟨hs, rfl⟩), rfl⟩
  · intro x hx
    exact ⟨mem_lift.2 (Or.inl hx), mem_lift.2 (Or.inl hx)⟩

theorem not_both {m h : ℕ} (s : Finset (Option (Fin m)) → Finset (Option (Fin m)))
    (hboth : ∀ x ∈ small m h, (x, false) ∈ region m h s ∧ (x, true) ∈ region m h s)
    (x : Finset (Fin m)) (hx : x ∈ shell m h)
    (h0 : (x, false) ∈ region m h s) (h1 : (x, true) ∈ region m h s) : False := by
  rw [mem_shell] at hx
  obtain ⟨E, hEdef⟩ : ∃ E, E = enc x true := ⟨_, rfl⟩
  have hE : E ∈ scopes m h := by rw [mem_scopes, hEdef, card_enc, hx]; simp
  obtain ⟨p, hp⟩ : ∃ p, s E ∩ E = p := ⟨_, rfl⟩
  have hpE : p ⊆ E := hp ▸ inter_subset_right
  have hyx : dec p ⊆ x := by
    intro i hi
    have h2 : some i ∈ p := by simpa [dec] using hi
    have h3 := hpE h2
    rwa [hEdef, mem_enc_some] at h3
  have hmem : (dec p, decide (none ∈ p)) ∈ region m h s := by
    by_cases hyx' : dec p = x
    · rw [hyx']
      generalize decide (none ∈ p) = bb
      cases bb
      · exact h0
      · exact h1
    · have hlt : (dec p).card < h := by
        rw [← hx]
        exact card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hyx, hyx'⟩)
      have h4 := hboth _ (mem_small.2 hlt)
      generalize decide (none ∈ p) = bb
      cases bb
      · exact h4.1
      · exact h4.2
  rw [mem_region] at hmem
  apply hmem E hE
  show enc (dec p) (decide (none ∈ p)) ∩ E = s E ∩ E
  rw [enc_dec, hp]
  exact inter_eq_left.2 hpE

theorem family_sub {m h : ℕ} (R : Finset (Finset (Fin m) × Bool)) (hR : R ∈ family m h) :
    ∃ F ∈ (shell m h).powerset, lift m h F = R := by
  rw [family, mem_filter, allRegions, mem_image] at hR
  obtain ⟨⟨s, _, rfl⟩, hproj, hboth⟩ := hR
  refine ⟨(shell m h).filter (fun x => (x, true) ∈ region m h s),
    mem_powerset.2 (filter_subset _ _), ?_⟩
  ext ⟨x, b⟩
  rw [mem_lift]
  simp only [mem_filter]
  constructor
  · rintro (hs | ⟨hs, rfl⟩)
    · cases b
      · exact (hboth x hs).1
      · exact (hboth x hs).2
    · by_cases ht : (x, true) ∈ region m h s
      · simp [hs, ht]
      · have h5 : x ∈ (region m h s).image Prod.fst := by
          rw [hproj]; exact mem_union_right _ hs
        rw [mem_image] at h5
        obtain ⟨⟨y, b'⟩, hy, hyx⟩ := h5
        simp only at hyx
        subst hyx
        cases b'
        · simpa [ht] using hy
        · exact absurd hy ht
  · intro hxb
    have h5 : x ∈ small m h ∪ shell m h := by
      rw [← hproj]; exact mem_image_of_mem Prod.fst hxb
    rcases mem_union.1 h5 with hs | hs
    · exact Or.inl hs
    · right
      refine ⟨hs, ?_⟩
      cases b
      · have h6 : (x, true) ∉ region m h s := fun ht => not_both s hboth x hs hxb ht
        simp [h6]
      · simp [hs, hxb]

theorem sauer_aux {α : Type*} [DecidableEq α] (𝒜 T : Finset (Finset α))
    (hT : ∀ s, 𝒜.Shatters s → s ∈ T) : 𝒜.card ≤ T.card :=
  (card_le_card_shatterer 𝒜).trans (card_le_card (fun s hs => hT s (mem_shatterer.1 hs)))

theorem part1 (m h : ℕ) :
    ∀ R ∈ allRegions m h, R.card ≤ 2 * (small m h).card + (shell m h).card := by
  intro R hR
  rw [allRegions, mem_image] at hR
  obtain ⟨s, _, rfl⟩ := hR
  have hinj : Set.InjOn (fun xb : Finset (Fin m) × Bool => enc xb.1 xb.2) ↑(region m h s) := by
    rintro ⟨x, b⟩ _ ⟨y, c⟩ _ hxy
    obtain ⟨h1, h2⟩ := enc_inj hxy
    exact Prod.ext h1 h2
  rw [← card_image_of_injOn hinj, ← card_lift (m := m) (h := h) ∅]
  refine le_trans ?_ (card_image_le (f := fun xb : Finset (Fin m) × Bool => enc xb.1 xb.2))
  apply sauer_aux
  intro c hc
  have hch : c.card ≤ h := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨E, hEc, hEcard⟩ := exists_subset_card_eq (show h + 1 ≤ c.card by omega)
    have hsh := hc.mono_right hEc
    obtain ⟨u, hu, hEu⟩ := hsh (inter_subset_right : s E ∩ E ⊆ E)
    rw [mem_image] at hu
    obtain ⟨⟨x, b⟩, hxb, rfl⟩ := hu
    rw [mem_region] at hxb
    apply hxb E (mem_scopes.2 hEcard)
    rw [inter_comm]
    exact hEu
  rw [mem_image]
  refine ⟨(dec c, decide (none ∈ c)), ?_, enc_dec c⟩
  rw [mem_lift]
  have hcd := card_dec c
  by_cases hn : none ∈ c
  · left
    rw [mem_small]
    rw [if_pos hn] at hcd
    show (dec c).card < h
    omega
  · rw [if_neg hn] at hcd
    by_cases hlt : (dec c).card < h
    · left; exact mem_small.2 hlt
    · right
      refine ⟨mem_shell.2 (by show (dec c).card = h; omega), ?_⟩
      simp [hn]

theorem part2 (m h : ℕ) : family m h = (shell m h).powerset.image (lift m h) := by
  ext R
  rw [mem_image]
  constructor
  · intro hR
    exact family_sub R hR
  · rintro ⟨F, _, rfl⟩
    exact lift_mem_family F

theorem part3 (m h : ℕ) :
    ∀ R ∈ family m h, R.card = 2 * (small m h).card + (shell m h).card := by
  intro R hR
  obtain ⟨F, _, rfl⟩ := family_sub R hR
  exact card_lift F

theorem lift_sub {m h : ℕ} {F G : Finset (Finset (Fin m))} (hF : F ⊆ shell m h)
    (hFG : lift m h F = lift m h G) : F ⊆ G := by
  intro x hx
  have h1 : (x, true) ∈ lift m h F := mem_lift.2 (Or.inr ⟨hF hx, by simp [hx]⟩)
  rw [hFG, mem_lift] at h1
  rcases h1 with hs | ⟨_, hb⟩
  · exact absurd (hF hx) (fun h2 => disj_small_shell hs h2)
  · simpa using hb

theorem lift_injOn (m h : ℕ) : Set.InjOn (lift m h) ↑((shell m h).powerset) := by
  intro F hF G hG hFG
  have hF' : F ⊆ shell m h := mem_powerset.1 (mem_coe.1 hF)
  have hG' : G ⊆ shell m h := mem_powerset.1 (mem_coe.1 hG)
  exact Subset.antisymm (lift_sub hF' hFG) (lift_sub hG' hFG.symm)

theorem part4 (m h : ℕ) : ∀ j : ℕ, ((family m h).filter (fun R =>
    (R.filter (fun xb => xb.2 = true)).card = (small m h).card + j)).card =
      Nat.choose (shell m h).card j := by
  intro j
  rw [part2, filter_image, card_image_of_injOn, ← card_powersetCard]
  · congr 1
    ext F
    simp only [mem_filter, mem_powerset, mem_powersetCard]
    constructor
    · rintro ⟨hF, hc⟩
      rw [true_count F hF] at hc
      exact ⟨hF, by omega⟩
    · rintro ⟨hF, hc⟩
      refine ⟨hF, ?_⟩
      rw [true_count F hF]
      omega
  · exact (lift_injOn m h).mono (coe_subset.2 (filter_subset _ _))

end PEqualNP.Outside.L_lib_1182_aux

theorem PEqualNP.Outside.L_lib_1182 : ∀ (m h : Nat),
  let Site := Option (Fin m)
  let Word := Finset (Fin m)
  let Scope := Finset Site
  let scopes := (Finset.univ : Finset Site).powersetCard (h + 1)
  let words := (Finset.univ : Finset Word)
  let small := words.filter (fun x => x.card < h)
  let shell := words.filter (fun x => x.card = h)
  let encode := fun (x : Word) (b : Bool) =>
    let old := x.image (fun i => (some i : Site))
    if b then insert none old else old
  let domain := (Finset.univ : Finset (Word × Bool))
  let region := fun (s : Scope → Scope) => domain.filter (fun xb =>
    ∀ E ∈ scopes, encode xb.1 xb.2 ∩ E ≠ s E ∩ E)
  let allRegions := (Finset.univ : Finset (Scope → Scope)).image region
  let family := allRegions.filter (fun R =>
    R.image Prod.fst = small ∪ shell ∧ ∀ x ∈ small, (x, false) ∈ R ∧ (x, true) ∈ R)
  let lift := fun (F : Finset Word) => domain.filter (fun xb =>
    xb.1 ∈ small ∨ (xb.1 ∈ shell ∧ xb.2 = decide (xb.1 ∈ F)))
  (∀ R ∈ allRegions, R.card ≤ 2 * small.card + shell.card) ∧
  family = shell.powerset.image lift ∧
  (∀ R ∈ family, R.card = 2 * small.card + shell.card) ∧
  (∀ j : Nat, (family.filter (fun R =>
    (R.filter (fun xb => xb.2 = true)).card = small.card + j)).card = Nat.choose shell.card j) := by
  intro m h
  exact ⟨PEqualNP.Outside.L_lib_1182_aux.part1 m h, PEqualNP.Outside.L_lib_1182_aux.part2 m h,
    PEqualNP.Outside.L_lib_1182_aux.part3 m h, PEqualNP.Outside.L_lib_1182_aux.part4 m h⟩

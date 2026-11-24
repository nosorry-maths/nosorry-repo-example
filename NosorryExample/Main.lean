import NosorryExample.Extra
/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 96

**Verbatim statement (WOWII #96, status O):**
> If G is a simple connected graph, then α(G) ≤ 1 + minimum dist_even(v)*(maximum of λ(v) -1)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj96


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uhd.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture96

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [Fintype α] [DecidableEq α] [Nontrivial α] in
private lemma exists_pred_of_dist_pos {G : SimpleGraph α} (h : G.Connected) {v u : α}
    (hu : 0 < G.dist v u) :
    ∃ w : α, G.Adj w u ∧ G.dist v w + 1 = G.dist v u := by
  obtain ⟨p, hp⟩ := (h v u).exists_walk_length_eq_dist
  cases hr : p.reverse with
  | nil =>
    have hlen : p.reverse.length = 0 := by rw [hr]; rfl
    rw [Walk.length_reverse, hp] at hlen
    omega
  | @cons _ w _ hadj q =>
    refine ⟨w, hadj.symm, ?_⟩
    have hlen : q.length + 1 = G.dist v u := by
      have h1 : p.reverse.length = q.length + 1 := by rw [hr]; rfl
      rw [Walk.length_reverse, hp] at h1
      exact h1.symm
    have hle1 : G.dist v w ≤ q.length := by
      have := G.dist_le q.reverse
      simpa using this
    have hle2 : G.dist v u ≤ G.dist v w + 1 := by
      obtain ⟨r, hr_len⟩ := (h v w).exists_walk_length_eq_dist
      have := G.dist_le (r.concat hadj.symm)
      simpa [hr_len] using this
    omega

omit [Nontrivial α] in
private lemma card_le_indepNeighborsCard {G : SimpleGraph α} (w : α) (S : Finset α)
    (hN : ∀ x ∈ S, G.Adj w x) (hI : G.IsIndepSet (S : Set α)) :
    S.card ≤ indepNeighborsCard G w := by
  classical
  let f : {x // x ∈ S} → G.neighborSet w := fun x => ⟨x.1, hN x.1 x.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : G.neighborSet w => z.1) hab)
  let S' : Finset (G.neighborSet w) := S.attach.image f
  have hcard : S'.card = S.card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
  have hI' : (G.induce (G.neighborSet w)).IsIndepSet (S' : Set (G.neighborSet w)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, S', Finset.mem_image, Finset.mem_attach, true_and,
      Subtype.exists] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hxy : x ≠ y := fun hxy => hab (Subtype.ext hxy)
    exact hI hx hy hxy
  rw [← hcard]
  exact hI'.card_le_indepNum

/--
WOWII [Conjecture 96](http://cms.uhd.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G` on at least two vertices,
`α(G) ≤ 1 + min_v distEven(v) · (max_v l(v) - 1)`
where `α(G) = G.indepNum` is the independence number,
`distEven(v)` is the number of vertices at even distance from `v`, and
`max_v l(v)` is the maximum independence number of a vertex neighbourhood.

We record the nontrivial-graph version: the literal source inequality fails on $K_1$,
where the independence number and even-distance count are both one, but the maximum
local independence number is zero, giving $1 ≤ 0$.
-/
@[category research open, AMS 5]
theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  classical
  intro minDistEven maxL
  have hmin_mem : minDistEven ∈ Finset.univ.image (distEven G) := Finset.min'_mem _ _
  obtain ⟨v, -, hv_eq⟩ := Finset.mem_image.mp hmin_mem
  have hmax_le : ∀ w : α, indepNeighborsCard G w ≤ maxL := fun w =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  have hmax_pos : 1 ≤ maxL := by
    obtain ⟨u, huv⟩ := exists_ne v
    have hdist_pos : 0 < G.dist v u := (h v u).pos_dist_of_ne huv.symm
    obtain ⟨w, hw, -⟩ := exists_pred_of_dist_pos h hdist_pos
    have h1 : 1 ≤ indepNeighborsCard G u := by
      have := card_le_indepNeighborsCard u {w}
        (by intro x hx; rw [Finset.mem_singleton.mp hx]; exact hw.symm)
        (by simp [SimpleGraph.IsIndepSet])
      simpa using this
    exact le_trans h1 (hmax_le u)
  by_cases hM1 : maxL = 1
  · have hclique : ∀ x y : α, x ≠ y → G.Adj x y := by
      intro x y hxy
      by_contra hnot
      obtain ⟨p, hp⟩ := (h x y).exists_walk_length_eq_dist
      match p with
      | .nil => exact hxy rfl
      | .cons h1 .nil => exact hnot h1
      | .cons (v := z) h1 (.cons (v := w) h2 q) =>
        have hxw : x ≠ w := by
          intro hxw
          subst hxw
          have hle := G.dist_le q
          simp only [Walk.length_cons] at hp
          omega
        have hnot_xw : ¬ G.Adj x w := by
          intro hadj
          have hle := G.dist_le (Walk.cons hadj q)
          simp only [Walk.length_cons] at hp hle
          omega
        have h2card : ({x, w} : Finset α).card = 2 := Finset.card_pair hxw
        have h2le : ({x, w} : Finset α).card ≤ indepNeighborsCard G z := by
          apply card_le_indepNeighborsCard z {x, w}
          · intro a ha
            rcases Finset.mem_insert.mp ha with rfl | ha
            · exact h1.symm
            · rw [Finset.mem_singleton.mp ha]; exact h2
          · intro a ha b hb hab
            simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact (hab rfl).elim
            · exact hnot_xw
            · exact fun h' => hnot_xw h'.symm
            · exact (hab rfl).elim
        have := le_trans (h2card ▸ h2le) (hmax_le z)
        omega
    have hind : G.indepNum ≤ 1 := by
      obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
      rw [← hI.card_eq]
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      by_contra hab
      exact hI.isIndepSet ha hb hab (hclique a b hab)
    rw [hM1]
    push_cast
    have : (G.indepNum : ℝ) ≤ 1 := by exact_mod_cast hind
    linarith
  · have hM2 : 2 ≤ maxL := by omega
    obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    let E : Finset α := Finset.univ.filter fun w => Even (G.dist v w)
    have hE_card : E.card = minDistEven := by
      rw [← hv_eq, distEven]
    have hvE : v ∈ E := by simp [E]
    let Ieven : Finset α := I.filter fun u => Even (G.dist v u)
    let Iodd : Finset α := I.filter fun u => ¬ Even (G.dist v u)
    have hI_split : I.card = Ieven.card + Iodd.card := by
      have hdisj : Disjoint Ieven Iodd := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
      have hunion : Ieven ∪ Iodd = I := by
        ext u
        simp only [Finset.mem_union, Finset.mem_filter, Ieven, Iodd]
        tauto
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hIeven_eq : Ieven = E ∩ I := by
      ext u
      simp [Ieven, E, and_comm]
    have hpred : ∀ u ∈ Iodd, ∃ w : α, G.Adj w u ∧ G.dist v w + 1 = G.dist v u := by
      intro u hu
      have hodd : ¬ Even (G.dist v u) := (Finset.mem_filter.mp hu).2
      have hpos : 0 < G.dist v u := by
        by_contra h0
        have : G.dist v u = 0 := by omega
        rw [this] at hodd
        exact hodd ⟨0, rfl⟩
      exact exists_pred_of_dist_pos h hpos
    let parent : α → α := fun u =>
      if hu : u ∈ Iodd then Classical.choose (hpred u hu) else v
    have hparent_adj : ∀ u ∈ Iodd, G.Adj (parent u) u := by
      intro u hu
      simp only [parent, dif_pos hu]
      exact (Classical.choose_spec (hpred u hu)).1
    have hparent_dist : ∀ u ∈ Iodd, G.dist v (parent u) + 1 = G.dist v u := by
      intro u hu
      simp only [parent, dif_pos hu]
      exact (Classical.choose_spec (hpred u hu)).2
    have hparent_mem : ∀ u ∈ Iodd, parent u ∈ E \ I := by
      intro u hu
      have huI : u ∈ I := (Finset.mem_filter.mp hu).1
      have hodd : ¬ Even (G.dist v u) := (Finset.mem_filter.mp hu).2
      have hd := hparent_dist u hu
      have heven : Even (G.dist v (parent u)) := by
        rw [Nat.even_iff] at hodd ⊢
        omega
      have hnotI : parent u ∉ I := by
        intro hpI
        have hne : parent u ≠ u := (hparent_adj u hu).ne
        exact hI.isIndepSet hpI huI hne (hparent_adj u hu)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, heven⟩, hnotI⟩
    have hfiber_le : ∀ w ∈ E \ I,
        (Iodd.filter fun u => parent u = w).card ≤ if w = v then maxL else maxL - 1 := by
      intro w hw
      let S := Iodd.filter fun u => parent u = w
      have hS_sub : S ⊆ I := fun u hu => (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1
      have hS_adj : ∀ u ∈ S, G.Adj w u := by
        intro u hu
        have hu1 := (Finset.mem_filter.mp hu).1
        have hu2 := (Finset.mem_filter.mp hu).2
        rw [← hu2]
        exact hparent_adj u hu1
      have hS_indep : G.IsIndepSet (S : Set α) := hI.isIndepSet.mono (Finset.coe_subset.mpr hS_sub)
      by_cases hwv : w = v
      · rw [if_pos hwv]
        exact le_trans (card_le_indepNeighborsCard w S hS_adj hS_indep) (hmax_le w)
      · rw [if_neg hwv]
        have hw_pos : 0 < G.dist v w := (h v w).pos_dist_of_ne (Ne.symm hwv)
        obtain ⟨q, hqw, hqdist⟩ := exists_pred_of_dist_pos h hw_pos
        have hq_not_mem : q ∉ S := by
          intro hqS
          have hq1 := (Finset.mem_filter.mp hqS).1
          have hq2 := (Finset.mem_filter.mp hqS).2
          have hd := hparent_dist q hq1
          rw [hq2] at hd
          omega
        have hq_not_adj : ∀ u ∈ S, ¬ G.Adj q u := by
          intro u hu hadj
          have hu1 := (Finset.mem_filter.mp hu).1
          have hu2 := (Finset.mem_filter.mp hu).2
          have hd := hparent_dist u hu1
          rw [hu2] at hd
          obtain ⟨r, hr⟩ := (h v q).exists_walk_length_eq_dist
          have hle := G.dist_le (r.concat hadj)
          simp only [Walk.length_concat, hr] at hle
          omega
        have hinsert_card : (insert q S).card = S.card + 1 := Finset.card_insert_of_notMem hq_not_mem
        have hinsert_le : (insert q S).card ≤ indepNeighborsCard G w := by
          apply card_le_indepNeighborsCard w (insert q S)
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hqw.symm
            · exact hS_adj x hx
          · intro a ha b hb hab
            simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
            rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · exact (hab rfl).elim
            · exact hq_not_adj b hb
            · exact fun h' => hq_not_adj a ha h'.symm
            · exact hS_indep ha hb hab
        have hle := le_trans (hinsert_card ▸ hinsert_le) (hmax_le w)
        change S.card ≤ maxL - 1
        omega
    have hIodd_eq : Iodd.card = ∑ w ∈ E \ I, (Iodd.filter fun u => parent u = w).card := by
      simpa using Finset.card_eq_sum_card_fiberwise (f := parent) (s := Iodd) (t := E \ I)
        (fun u hu => hparent_mem u hu)
    have hIodd_le : Iodd.card ≤ ∑ w ∈ E \ I, (if w = v then maxL else maxL - 1) := by
      rw [hIodd_eq]
      exact Finset.sum_le_sum hfiber_le
    have hE_split : (E ∩ I).card + (E \ I).card = E.card :=
      Finset.card_inter_add_card_sdiff E I
    have hnat : I.card ≤ 1 + E.card * (maxL - 1) := by
      by_cases hv_sdiff : v ∈ E \ I
      · have hsum_eval : (∑ w ∈ E \ I, if w = v then maxL else maxL - 1) =
            1 + (E \ I).card * (maxL - 1) := by
          rw [← Finset.add_sum_erase _ _ hv_sdiff, if_pos rfl]
          have hrest : (∑ w ∈ (E \ I).erase v, if w = v then maxL else maxL - 1) =
              ((E \ I).erase v).card * (maxL - 1) := by
            rw [Finset.sum_congr rfl (fun w hw => if_neg (Finset.ne_of_mem_erase hw))]
            simp
          rw [hrest, Finset.card_erase_of_mem hv_sdiff]
          have hpos : 1 ≤ (E \ I).card := Finset.one_le_card.mpr ⟨v, hv_sdiff⟩
          have : (E \ I).card = ((E \ I).card - 1) + 1 := by omega
          nth_rw 2 [this]
          have : maxL = 1 + (maxL - 1) := by omega
          linarith
        have hIeven_le : Ieven.card ≤ (E ∩ I).card * (maxL - 1) := by
          rw [hIeven_eq]
          exact Nat.le_mul_of_pos_right _ (by omega)
        calc
          I.card = Ieven.card + Iodd.card := hI_split
          _ ≤ (E ∩ I).card * (maxL - 1) + (1 + (E \ I).card * (maxL - 1)) :=
            Nat.add_le_add hIeven_le (hsum_eval ▸ hIodd_le)
          _ = 1 + ((E ∩ I).card + (E \ I).card) * (maxL - 1) := by ring
          _ = 1 + E.card * (maxL - 1) := by rw [hE_split]
      · have hv_inter : v ∈ E ∩ I := by
          have hvI : v ∈ I := by
            by_contra hnot
            exact hv_sdiff (Finset.mem_sdiff.mpr ⟨hvE, hnot⟩)
          exact Finset.mem_inter.mpr ⟨hvE, hvI⟩
        have hsum_eval : (∑ w ∈ E \ I, if w = v then maxL else maxL - 1) =
            (E \ I).card * (maxL - 1) := by
          rw [Finset.sum_congr rfl (fun w hw => if_neg (fun hwv : w = v => hv_sdiff (hwv ▸ hw)))]
          simp
        have hIeven_le : Ieven.card ≤ 1 + ((E ∩ I).card - 1) * (maxL - 1) := by
          rw [hIeven_eq]
          have hpos : 1 ≤ (E ∩ I).card := Finset.one_le_card.mpr ⟨v, hv_inter⟩
          have h1 : (E ∩ I).card - 1 ≤ ((E ∩ I).card - 1) * (maxL - 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          omega
        have hE_pos : 1 ≤ (E ∩ I).card := Finset.one_le_card.mpr ⟨v, hv_inter⟩
        calc
          I.card = Ieven.card + Iodd.card := hI_split
          _ ≤ (1 + ((E ∩ I).card - 1) * (maxL - 1)) + (E \ I).card * (maxL - 1) :=
            Nat.add_le_add hIeven_le (hsum_eval ▸ hIodd_le)
          _ ≤ 1 + ((E ∩ I).card + (E \ I).card) * (maxL - 1) := by
            have hle : ((E ∩ I).card - 1) + (E \ I).card ≤ (E ∩ I).card + (E \ I).card := by omega
            have := Nat.mul_le_mul_right (maxL - 1) hle
            linarith
          _ = 1 + E.card * (maxL - 1) := by rw [hE_split]
    rw [hI.card_eq, hE_card] at hnat
    have hreal : (G.indepNum : ℝ) ≤ ((1 + minDistEven * (maxL - 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast [Nat.cast_sub hmax_pos] at hreal
    linarith

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (G.indepNum : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture96

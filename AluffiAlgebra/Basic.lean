import Mathlib

namespace Chapter2

/--
  Exercise 1.3. Prove that the inverse of gh is h^-1g^-1 for all elements g, h in a group G.
  This result is already in Mathlib under "mul_inv_rev" - we can prove from first principles.
-/
theorem mul_inverse_reverse {G: Type*} [Group G] (g h: G) : (g * h)⁻¹ = h⁻¹*g⁻¹ := by
  have h1 : (g * h) * (h⁻¹ * g⁻¹) = 1 := by
    calc (g * h) * (h⁻¹ * g⁻¹) = g * (h*h⁻¹) * g⁻¹ := by group
    _ = g * 1 * g⁻¹   := by rw[mul_inv_cancel h]
    _ = g * g⁻¹       := by rw[mul_one]
    _ = 1             := by rw[mul_inv_cancel g]
  have h2: h⁻¹*g⁻¹ = (g * h)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right h1
  symm
  exact h2


/--
  Exercise 1.4. Suppose that g^2=e for all elements g of G, prove that G is commutative.
-/

theorem comm_of_sq_eq_one {G: Type*} [Group G] (square_is_one : ∀ g : G, g * g = 1)
: ∀ a b : G, a * b = b * a := by
  intro a b
  have a_is_own_inverse : a * a = 1 := square_is_one a
  have b_is_own_inverse : b * b = 1 := square_is_one b
  have ab_is_own_inverse : (a*b) * (a*b) = 1 := square_is_one (a*b)
  have expansion_1 : a * (a * b * (a * b)) * b = a * b := by
    rw [ab_is_own_inverse, mul_one]
  have expansion_2 : a * a * (b * a) * b * b = a*b := by
    rw [← expansion_1]
    simp only [← mul_assoc]
  rw [a_is_own_inverse, one_mul, mul_assoc, b_is_own_inverse, mul_one] at expansion_2
  rw [← expansion_2]

/--
  Exercise 1.7. Let g be an element of finite order. If g^N = e,
  then N is a multiple of |g|. This is actually a theorem - orderOf_dvd_iff_pow_eq_one.
-/
lemma divides_implies_pow {G : Type*} [Group G] (g : G) (N : ℕ) (h : orderOf g ∣ N) :
    g^N = 1 := by
  obtain ⟨k, hk⟩ := h
  rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]

lemma pow_implies_divides {G : Type*} [Group G] (g : G) (finit_order : IsOfFinOrder g) (N : ℕ)
    (h : g ^ N = 1) : orderOf g ∣ N := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have ord_pos : 0 < orderOf g := IsOfFinOrder.orderOf_pos finit_order
  have eq : N = orderOf g * (N / orderOf g) + N % orderOf g := (Nat.div_add_mod N (orderOf g)).symm
  rw [eq, pow_add, pow_mul, pow_orderOf_eq_one, one_pow, one_mul] at h
  have remainder_lt : N % orderOf g < orderOf g := Nat.mod_lt N ord_pos
  have : orderOf g ∣ N % orderOf g := orderOf_dvd_of_pow_eq_one h
  exact Nat.eq_zero_of_dvd_of_lt this remainder_lt

theorem pow_eq_one_iff_multiplier_order1 {G : Type*} [Group G]
    (g : G) (finit_order : IsOfFinOrder g) (N : ℕ) :
    g^N = 1 ↔ orderOf g ∣ N := by
  exact Iff.intro (pow_implies_divides g finit_order N) (divides_implies_pow g N)

/-
  Exercise 1.8. Let G be a finite abelian group with exactly one elemnt of order 2.
  Prove that the product of all elements in ∏_{g∈G} g = f.
-/
theorem product_eq_unique_order_two {G: Type*}[CommGroup G][Fintype G]
  (f : G)(hf : orderOf f = 2)(h_unique : ∀ g : G, orderOf g = 2 → g=f) : ∏ g: G, g=f := by

  /- Basic facts about the element f -/
  have hf_ne_one: f ≠ 1 := by
    intro h; simp [h, orderOf_one] at hf

  have hf_inv: f⁻¹=f := by
    exact inv_eq_self_of_orderOf_eq_two hf

  /- Element of order not 1 or 2 have different inverse elements. -/
  have inv_not_equal: ∀ g : G, orderOf g ≠ 1 → orderOf g ≠ 2 → g⁻¹ ≠ g := by
    intro g hg1 hg2 h
    have hpos : 0 < orderOf g := orderOf_pos g
    have hle : orderOf g ≤ 2 := by
      apply orderOf_le_of_pow_eq_one (n := 2) (by omega)
      rw [sq]
      rw (occs := .pos [1]) [←  h]
      exact inv_mul_cancel g
    interval_cases (orderOf g) <;> simp_all


  let S_1 := Finset.univ.filter (fun g: G => orderOf g = 1)
  let S_2 := Finset.univ.filter (fun g: G => orderOf g = 2)
  let S_3 := Finset.univ.filter (fun g: G => orderOf g ≠ 1 ∧ orderOf g ≠ 2)

  have prod_S_1 : ∏ g ∈ S_1, g = 1 := by
    apply Finset.prod_eq_one
    intro g hg
    exact orderOf_eq_one_iff.mp (Finset.mem_filter.mp hg).2

  have prod_S_2 : ∏ g ∈ S_2, g = f := by
    have hS_2 : S_2 = {f} := by
      ext g; simp [S_2]
      exact ⟨h_unique g, fun h => h ▸ hf⟩
    simp [hS_2]


  have prod_S_3 : ∏ g ∈ S_3, g = 1 := by
    have hinv : ∀ g ∈ S_3, g⁻¹ ∈ S_3 := by
      intro g hg
      simp only [S_3, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact ⟨by rw [orderOf_inv]; exact hg.1,
            by rw [orderOf_inv]; exact hg.2⟩
    have hne : ∀ g ∈ S_3, g⁻¹ ≠ g := by
      intro g hg
      simp only [S_3, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      exact inv_not_equal g hg.1 hg.2
    exact Finset.prod_involution
      (fun g _ => g⁻¹)
      (fun g hg => by simp only [S_3, Finset.mem_filter,
                      Finset.mem_univ, true_and] at hg
                      exact mul_inv_cancel g)
      (fun g hg _ => hne g hg)
      (fun g hg => hinv g hg)
      (fun g _ => by simp)


  have decomposition_of_product : ∏ g : G,
    g = (∏ g ∈ S_1, g) * (∏ g ∈ S_2, g) * (∏ g ∈ S_3, g) := by
    sorry

  rw [decomposition_of_product, prod_S_1, prod_S_2, prod_S_3]
  simp


/-
  Exercise 1.9. Let G be a finite group of order n, and let m be the number of g ∈ G
  or order exactly 2. Prove that n-m is odd.
-/

/-
  Exercise 1.11. For all g, h ∈ G, the order of gh is equal to the order of hg.
-/


/-
  Exercise 1.14. If g and h commute and gcd(|g|, |h|) = 1, then |gh| = |g| · |h|.
-/

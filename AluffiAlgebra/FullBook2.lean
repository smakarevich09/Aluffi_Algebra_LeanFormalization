-- Chapter II: Groups, First Encounter
-- Lean formalization with proof outlines
--
-- NOTE (Aristotle): the original file used a small set of imports and referred to
-- many identifiers that do not exist in Mathlib (`IsProduct`, `IsIso`,
-- `UniversalProperty`, `≅`, `Circle`, `Dihedral`, `Coker`, `Aut`, `∞`, ...).
-- To make the file compile and to be able to discharge the sorries, the imports
-- were changed to `import Mathlib`.  Statements that were not well-formed have
-- been restated faithfully using genuine Mathlib notions (`MulEquiv` `≃*`,
-- `AddEquiv` `≃+`, `MonoidHom` `→*`, `AddMonoidHom` `→+`, `Nat.card`,
-- `Subgroup.index`, `DihedralGroup`, ...).  Statements that cannot be stated
-- faithfully with the available machinery, or that are simply false as written,
-- are preserved verbatim inside a block comment together with an explanation.

import Mathlib

open Function

namespace GroupTheory

-- ============================================================================
-- Section 1: Definition of Group
-- ============================================================================

-- Definition 1.2 is essentially Mathlib's Group definition
-- We outline key properties

section BasicGroupProperties

variable {G : Type*} [Group G]

/-
Proposition 1.6: The identity element is unique
-/
theorem identity_unique (h : G) (h_identity : ∀ g : G, g * h = g ∧ h * g = g) :
  h = 1 := by
  simpa using h_identity 1 |>.1

/-
Proposition 1.7: The inverse is unique
-/
theorem inverse_unique (g h₁ h₂ : G)
  (h1_inv : g * h₁ = 1 ∧ h₁ * g = 1)
  (h2_inv : g * h₂ = 1 ∧ h₂ * g = 1) :
  h₁ = h₂ := by
  rw [ eq_inv_of_mul_eq_one_right h1_inv.1, eq_inv_of_mul_eq_one_right h2_inv.1 ]

/-
Lemma 1.10: If g^n = 1 then |g| divides n
For finite order elements
-/
theorem order_dvd_of_pow_eq_one {g : G} {n : ℕ}
  (h : g ^ n = 1) (hn : n ≠ 0) :
  (orderOf g) ∣ n := by
  -- By definition of order, if $g^n = 1$, then the order of $g$ must divide $n$.
  apply orderOf_dvd_of_pow_eq_one; exact h

/-
Corollary 1.11: g^N = 1 iff N is multiple of |g|
-/
theorem pow_eq_one_iff_orderOf_dvd (g : G) (N : ℤ) :
  g ^ N = 1 ↔ (orderOf g : ℤ) ∣ N := by
  rw [ ← zpow_mod_orderOf, zpow_eq_one_iff_modEq ];
  simp +decide [ Int.ModEq, Int.emod_eq_zero_of_dvd ]

end BasicGroupProperties

-- ============================================================================
-- Section 1.5: Commutative Groups
-- ============================================================================

section CommutativeGroups

variable {G : Type*} [CommGroup G]

/-
Proposition 1.13: |g^m| = lcm(m, |g|) / m
-/
theorem order_pow_eq_div_gcd (g : G) (m : ℕ) (hm : m ≠ 0) :
  orderOf (g ^ m) = (Nat.lcm m (orderOf g)) / m := by
  rw [ orderOf_pow' ];
  · simp +decide [ Nat.lcm, Nat.gcd_comm ];
    rw [ Nat.div_div_eq_div_mul, mul_comm ];
    rw [ Nat.mul_div_mul_right _ _ ( Nat.pos_of_ne_zero hm ) ];
  · exact hm

/-
Proposition 1.14: If gh = hg then |gh| divides lcm(|g|, |h|)
-/
theorem order_mul_dvd_lcm_of_commute {g h : G} (hcomm : Commute g h) :
  orderOf (g * h) ∣ Nat.lcm (orderOf g) (orderOf h) := by
  convert Commute.orderOf_mul_dvd_lcm ( show Commute g h from hcomm ) using 1

end CommutativeGroups

-- ============================================================================
-- Section 2: Examples of Groups
-- ============================================================================

section Examples

/-
Example 2.3: Order of an element in Z/nZ.
NOTE: Z/nZ is an *additive* group, so the relevant notion is `addOrderOf`,
not the multiplicative `orderOf` used in the original statement.
-/
theorem order_mod_cast (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
  addOrderOf (m : ZMod n) = n / Nat.gcd m n := by
  convert ZMod.addOrderOf_coe m hn using 1;
  rw [ Nat.gcd_comm ]

-- Proposition 2.6: (Z/nZ)* forms a group under multiplication.
-- NOTE: a `theorem` must be `Prop`-valued, so this asserts that such a group
-- structure exists (it is provided by Mathlib).
theorem unit_group_mul_is_group (n : ℕ) : Nonempty (Group (Units (ZMod n))) := by
  exact ⟨inferInstance⟩

end Examples

-- ============================================================================
-- Section 3: The Category Grp
-- ============================================================================

section Homomorphisms

variable {G H : Type*} [Group G] [Group H]

-- Definition 3.1: Group homomorphism
def IsGroupHom (f : G → H) : Prop :=
  ∀ a b : G, f (a * b) = f a * f b

/-
Proposition 3.2: Homomorphisms preserve identity and inverses
-/
theorem hom_preserves_identity {f : G → H} (hf : IsGroupHom f) :
  f 1 = 1 := by
  simpa using hf 1 1

theorem hom_preserves_inv {f : G → H} (hf : IsGroupHom f) (g : G) :
  f g⁻¹ = (f g)⁻¹ := by
  exact eq_inv_of_mul_eq_one_right ( by rw [ ← hf, mul_inv_cancel, hom_preserves_identity hf ] )

-- Proposition 3.3: Trivial groups are initial and final in Grp.
-- (Kept as the placeholder `True` from the original outline; a faithful
-- statement would require the category `Grp` and `IsInitial`/`IsTerminal`.)
theorem trivial_is_initial_and_final : True := by
  trivial

/-
-- Proposition 3.4: Direct product is a product in Grp
-- ORIGINAL (does not compile: `IsProduct` is undefined).  A faithful statement
-- requires category theory (the universal property of the product in `Grp`).
theorem direct_product_is_product (G H : Type*) [Group G] [Group H] :
  IsProduct (G × H) := by
  sorry
-/

end Homomorphisms

-- ============================================================================
-- Section 4: Group Homomorphisms
-- ============================================================================

section HomomorphismProperties

variable {G H : Type*} [Group G] [Group H]

/-
Proposition 4.1: If φ : G → H is a homomorphism and g has finite order,
then |φ(g)| divides |g|
-/
theorem order_divides_order_of_hom {f : G → H} (hf : IsGroupHom f) (g : G) :
  (orderOf (f g)) ∣ (orderOf g) := by
  -- By definition of order, we know that $(f(g))^{orderOf g} = f(g^{orderOf g})$.
  have h_order : (f g) ^ orderOf g = f (g ^ orderOf g) := by
    induction' orderOf g with n ih <;> simp_all +decide [ pow_succ' ];
    · exact Eq.symm ( hom_preserves_identity hf );
    · rw [ hf ];
  exact orderOf_dvd_iff_pow_eq_one.mpr ( by rw [ h_order, pow_orderOf_eq_one, hom_preserves_identity hf ] )

/-
Proposition 4.3: A group homomorphism is an isomorphism iff it's a bijection.
NOTE: `IsIso` was undefined; "isomorphism" is rendered here as "admits a
two-sided homomorphism inverse".
-/
theorem hom_is_iso_iff_bijective {f : G → H} (hf : IsGroupHom f) :
  (∃ g : H → G, IsGroupHom g ∧ (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y))
    ↔ Function.Bijective f := by
  constructor;
  · exact fun ⟨ g, hg, hg₁, hg₂ ⟩ => ⟨ fun x y hxy => by rw [ ← hg₁ x, ← hg₁ y, hxy ], fun y => ⟨ g y, hg₂ y ⟩ ⟩;
  · intro h;
    obtain ⟨g, hg⟩ : ∃ g : H → G, Function.LeftInverse g f ∧ Function.RightInverse g f := by
      exact Function.bijective_iff_has_inverse.mp h;
    refine' ⟨ g, _, hg.1, hg.2 ⟩;
    intro x y;
    exact h.injective ( by have := hf ( g x ) ( g y ) ; have := hg.2 x; have := hg.2 y; have := hg.2 ( x * y ) ; aesop )

/-
Example 4.2: No nontrivial homomorphisms Z/nZ → Z.
NOTE: these are *additive* group homomorphisms (`→+`); `n ≠ 0` is needed
(for `n = 0`, `ZMod 0 = ℤ` admits nontrivial homs to `ℤ`).
-/
theorem no_nontrivial_hom_to_integers (n : ℕ) [NeZero n] :
  ∀ f : ZMod n →+ ℤ, ∀ x : ZMod n, f x = 0 := by
  intro f x; have := f.map_nsmul x n; simp_all +decide [ NeZero.ne ] ;

/-
Example 4.2: No nontrivial homomorphisms C_m → C_n if gcd(m,n)=1.
NOTE: rendered as additive group homomorphisms `→+`.
-/
theorem no_nontrivial_hom_coprime_cyclic (m n : ℕ) [NeZero n]
    (hcoprime : Nat.Coprime m n) :
  ∀ f : ZMod m →+ ZMod n, ∀ x : ZMod m, f x = 0 := by
  intro f x
  have h_mul : m • f x = 0 := by
    rw [ ← f.map_nsmul, nsmul_eq_mul ];
    cases m <;> aesop;
  have h_mul_n : n • f x = 0 := by
    simp +decide [ ← ZMod.natCast_eq_zero_iff ];
  have := Nat.gcd_eq_gcd_ab m n; simp_all +decide [ ← mul_assoc, mul_comm ] ;
  replace this := congr_arg ( fun z : ℤ => z • f x ) this ; simp_all +decide [ mul_assoc, mul_left_comm, add_smul ] ;

end HomomorphismProperties

-- ============================================================================
-- Section 5: Free Groups
-- ============================================================================

section FreeGroups

-- We use Mathlib's free group definition
variable {α : Type*}

/-
Proposition 5.2: The concrete free group satisfies the universal property.
NOTE: `UniversalProperty` was undefined; the universal property is stated
concretely as the existence and uniqueness of the induced homomorphism.
-/
theorem free_group_universal_property (α : Type*) {H : Type*} [Group H] (f : α → H) :
  ∃! F : FreeGroup α →* H, ∀ a, F (FreeGroup.of a) = f a := by
  use FreeGroup.lift f;
  refine' ⟨ _, _ ⟩; all_goals aesop

/-
Claim 5.4: Z^n is the free abelian group on n generators.
NOTE: `≅` was undefined; rendered as an additive-group isomorphism `≃+`.
-/
theorem free_abelian_group_power (n : ℕ) :
  Nonempty (FreeAbelianGroup (Fin n) ≃+ (Fin n → ℤ)) := by
  refine' ⟨ _ ⟩;
  exact ( FreeAbelianGroup.equivFinsupp _ ).trans ( Finsupp.addEquivFunOnFinite )

/-
Proposition 5.6: Fab(A) ≅ Z^A (finitely supported).
NOTE: the original wrote `α → ℤ`, but as the comment says the correct object
is the *finitely supported* functions `α →₀ ℤ`.  Rendered as `≃+`.
-/
theorem free_abelian_universal (α : Type*) :
  Nonempty (FreeAbelianGroup α ≃+ (α →₀ ℤ)) := by
  refine' ⟨ _ ⟩;
  convert FreeAbelianGroup.equivFinsupp α

end FreeGroups

-- ============================================================================
-- Section 6: Subgroups
-- ============================================================================

section Subgroups

variable {G : Type*} [Group G]

-- Definition 6.1 & Proposition 6.2: Subgroup criterion
def IsSubgroup (H : Set G) : Prop :=
  (1 ∈ H) ∧ (∀ a ∈ H, ∀ b ∈ H, a * b⁻¹ ∈ H)

-- Basic closure properties derived from the subgroup criterion.
theorem IsSubgroup.inv_mem {H : Set G} (hH : IsSubgroup H) {a : G} (ha : a ∈ H) :
    a⁻¹ ∈ H := by
  simpa using hH.2 1 hH.1 a ha

theorem IsSubgroup.mul_mem {H : Set G} (hH : IsSubgroup H) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  have := hH.2 a ha b⁻¹ (hH.inv_mem hb)
  simpa using this

/-
Lemma 6.3: Intersection of subgroups is a subgroup
-/
theorem intersection_subgroup {ι : Type*} {H : ι → Set G}
  (h : ∀ i, IsSubgroup (H i)) :
  IsSubgroup (⋂ i, H i) := by
  simp_all +decide [ IsSubgroup ]

/-
Lemma 6.4: Preimage of subgroup under homomorphism is subgroup
-/
theorem preimage_subgroup {H : Type*} [Group H] {f : G → H}
  (hf : IsGroupHom f) (S : Set H) (hs : IsSubgroup S) :
  IsSubgroup (f ⁻¹' S) := by
  refine' ⟨ _, _ ⟩;
  · exact hs.1 |> fun h => by simpa [ hom_preserves_identity hf ] using h;
  · simp_all +decide [ IsSubgroup ];
    intro a ha b hb;
    convert hs.2 _ ha _ hb using 1;
    have := hf a b⁻¹; have := hf b b⁻¹; simp_all +decide [ mul_assoc ] ;
    exact eq_inv_of_mul_eq_one_right ( this ▸ by rw [ hom_preserves_identity hf ] )

-- Definition 6.5: Kernel of homomorphism
def Kernel {H : Type*} [Group H] (f : G → H) : Set G :=
  {g : G | f g = 1}

/-
Lemma 6.6: Kernel is a subgroup
-/
theorem kernel_is_subgroup {H : Type*} [Group H] (f : G → H)
  (hf : IsGroupHom f) :
  IsSubgroup (Kernel f) := by
  constructor;
  · exact hom_preserves_identity hf;
  · unfold Kernel;
    simp_all +decide [ IsGroupHom ];
    intro a ha b hb; have := hf b⁻¹ b; simp_all +decide ;
    have := hf 1 1; aesop;

-- Definition 6.8: Subgroup generated by a subset
def Subgroup.generated (S : Set G) : Set G :=
  ⋂₀ {H : Set G | S ⊆ H ∧ IsSubgroup H}

/-
Closure of a subgroup under integer powers.
-/
theorem IsSubgroup.zpow_mem {H : Set G} (hH : IsSubgroup H) {a : G}
    (ha : a ∈ H) (n : ℤ) : a ^ n ∈ H := by
  induction' n using Int.induction_on with n ihn n ihn;
  · simpa using hH.1;
  · simp_all +decide [ zpow_add, IsSubgroup.mul_mem ];
  · have := hH.2 _ ihn _ ha; simp_all +decide [ zpow_sub, zpow_add ] ;

/-
The subgroup generated by a single element is exactly its set of integer powers.
-/
theorem Subgroup.generated_singleton (g : G) :
    Subgroup.generated ({g} : Set G) = {x : G | ∃ n : ℤ, x = g ^ n} := by
  refine' Set.Subset.antisymm _ _;
  · refine' Set.sInter_subset_of_mem _;
    refine' ⟨ _, _, _ ⟩ <;> simp +decide [ IsSubgroup ];
    · exact ⟨ 1, by simp +decide ⟩;
    · exact ⟨ 0, by simp +decide ⟩;
    · exact fun a b => ⟨ a - b, by group ⟩;
  · rintro x ⟨ n, rfl ⟩ H ⟨ h₁, h₂ ⟩;
    exact h₂.zpow_mem ( h₁ ( Set.mem_singleton g ) ) n

/-
-- Proposition 6.9: Subgroups of Z.
-- ORIGINAL.  The `IsSubgroup` predicate defined above is *multiplicative*
-- (it uses `1`, `*` and `⁻¹` from `[Group G]`), but the subgroups of `ℤ` meant
-- here are *additive*.  `IsSubgroup (H : Set ℤ)` therefore requires a
-- (nonexistent) multiplicative `Group ℤ` instance and does not typecheck.
-- A faithful statement would use Mathlib's `AddSubgroup ℤ`.
theorem subgroup_of_integers :
  ∀ H : Set ℤ, IsSubgroup H → ∃ d : ℕ, H = {n : ℤ | (d : ℤ) ∣ n} := by
  sorry

-- Proposition 6.11: Subgroups of Z/nZ.
-- ORIGINAL.  As with Proposition 6.9, `IsSubgroup` is *multiplicative* and
-- `ZMod n` is not a multiplicative group (`Group (ZMod n)` does not exist), so
-- this does not typecheck; the intended object is the additive group `ℤ/nℤ`.
theorem subgroup_of_mod_n (n : ℕ) :
  ∀ H : Set (ZMod n), IsSubgroup H → ∃ d : ℕ, d ∣ n := by
  sorry

Proposition 6.12: Monomorphisms characterized by trivial kernel
-/
theorem mono_iff_trivial_kernel {H : Type*} [Group H] (f : G → H)
  (hf : IsGroupHom f) :
  Function.Injective f ↔ Kernel f = {1} := by
  constructor <;> intro h;
  · ext x;
    constructor <;> intro hx <;> have := hf 1 x <;> aesop;
  · rw [ Set.ext_iff ] at h;
    intro x y hxy
    have h_eq : f (x * y⁻¹) = 1 := by
      simp_all +decide [ IsGroupHom, mul_inv_eq_one ];
      rw [ ← hf, mul_inv_cancel, show f 1 = 1 from by simpa using hf 1 1 ];
    simpa [ mul_inv_eq_one ] using h ( x * y⁻¹ ) |>.1 h_eq

end Subgroups

-- ============================================================================
-- Section 7: Quotient Groups and Normal Subgroups
-- ============================================================================

section NormalSubgroups

variable {G : Type*} [Group G]

-- Definition 7.1: Normal subgroup
-- NOTE: original wrote `∀ g ∈ G` (G is a type, not a set); corrected to `∀ g : G`.
def IsNormal (N : Set G) : Prop :=
  ∀ g : G, ∀ n ∈ N, g * n * g⁻¹ ∈ N

/-
Lemma 7.2: Kernel is normal
-/
theorem kernel_is_normal {H : Type*} [Group H] (f : G → H)
  (hf : IsGroupHom f) :
  IsNormal (Kernel f) := by
  intro g n hn; have := hf g n; have := hf n⁻¹ g; simp_all +decide [ mul_assoc, eq_inv_mul_iff_mul_eq ] ;
  simp_all +decide [ Kernel, IsGroupHom ];
  rw [ ← hf, mul_inv_cancel, show f 1 = 1 from by simpa using hf 1 1 ]

-- Definition 7.5: Left cosets
def LeftCoset (H : Set G) (a : G) : Set G :=
  {g : G | ∃ h ∈ H, g = a * h}

-- Right cosets (added: the original referenced `RightCoset` without defining it)
def RightCoset (H : Set G) (a : G) : Set G :=
  {g : G | ∃ h ∈ H, g = h * a}

/-
Proposition 7.6: Equivalence relation from subgroup
-/
theorem equiv_relation_from_subgroup (H : Set G) (hs : IsSubgroup H) :
  ∃ R : G → G → Prop, Equivalence R := by
  constructor;
  apply_rules [ Equivalence.mk ]; all_goals aesop

/-
Proposition 7.10: Normal iff left cosets = right cosets
-/
theorem normal_iff_lr_cosets (H : Set G) (hs : IsSubgroup H) :
  IsNormal H ↔ (∀ g : G, LeftCoset H g = RightCoset H g) := by
  constructor <;> intro h <;> simp_all +decide [ Set.ext_iff, LeftCoset, RightCoset ];
  · intro g x;
    constructor <;> rintro ⟨ y, hy, rfl ⟩;
    · exact ⟨ g * y * g⁻¹, h g y hy, by group ⟩;
    · exact ⟨ g⁻¹ * y * g, by simpa [ mul_assoc ] using h g⁻¹ y hy, by group ⟩;
  · intro g n hn; specialize h g ( g * n ) ; simp_all +decide [ eq_comm ] ;
    obtain ⟨ h, hh, hh' ⟩ := h; simp_all +decide [ mul_assoc, hs.1 ] ;

/-
-- Definition 7.11 & Theorem 7.12: Quotient group universal property.
-- ORIGINAL.  This is faithfully stated but proving it from the ad-hoc,
-- `Set`-based definitions above would amount to reconstructing the entire
-- quotient-group machinery (which Mathlib provides as `QuotientGroup`).
-- Left in comment form as it is out of scope for this file.
theorem quotient_universal_property (N : Set G) (hn : IsNormal N) :
  ∃ (Q : Type*) (inst : Group Q) (π : G → Q),
    IsGroupHom π ∧ (∀ n ∈ N, π n = 1) ∧
    (∀ {H : Type*} [Group H] (f : G → H),
      IsGroupHom f → (∀ n ∈ N, f n = 1) →
      ∃! f̃ : Q → H, IsGroupHom f̃ ∧ (∀ g : G, f̃ (π g) = f g)) := by
  sorry
-/

end NormalSubgroups

-- ============================================================================
-- Section 8: Canonical Decomposition and Lagrange's Theorem
-- ============================================================================

section IsomorphismTheorems

variable {G H : Type*} [Group G] [Group H]

/-
-- Theorem 8.1: First Isomorphism Theorem
-- ORIGINAL (does not compile: `/` on types, `Image`, `≅` are undefined).
-- Mathlib: `QuotientGroup.quotientKerEquivRange`.
theorem first_isomorphism_theorem (f : G → H) (hf : IsGroupHom f) :
  G / Kernel f ≅ Image f := by
  sorry

-- Corollary 8.2: Surjective hom implies quotient isomorphic to target.
-- ORIGINAL (does not compile).  Mathlib: `QuotientGroup.quotientKerEquivOfSurjective`.
theorem surjective_hom_iso (f : G → H) (hf : IsGroupHom f)
  (hsurj : Surjective f) :
  G / Kernel f ≅ H := by
  sorry

-- Example 8.4: D_6 ≅ S_3.
-- ORIGINAL (does not compile: `Dihedral`, `≅` undefined).  See the faithful
-- restatement `dihedral_3_iso_sym_3` below.
theorem dihedral_6_iso_sym_3 : Dihedral 3 ≅ Equiv.Perm (Fin 3) := by
  sorry

-- Example 8.7: R/Z ≅ circle group.
-- ORIGINAL (does not compile).  Mathlib: `AddCircle`, `Circle`.
theorem quotient_reals_mod_integers : (ℝ ⧸ ℤ) ≅ Circle := by
  sorry

-- Proposition 8.9: Lattice correspondence for quotient.
-- ORIGINAL (does not compile: `≅` between subgroup lattices undefined).
-- Mathlib: `QuotientGroup.comapMk'OrderIso`.
theorem lattice_correspondence_quotient (N : Set G) (hn : IsNormal N) :
  {H : Set G | N ⊆ H ∧ IsSubgroup H} ≅
  {H : Set (G ⧸ N) | IsSubgroup H} := by
  sorry

-- Proposition 8.10: Third Isomorphism Theorem.
-- ORIGINAL (does not compile: `⧸` needs `Subgroup`, not `Set`; `≅` undefined).
-- Mathlib: `QuotientGroup.quotientQuotientEquivQuotient`.
theorem third_isomorphism_theorem (N K : Set G)
  (hn : IsNormal N) (hk : IsSubgroup K) (hnk : N ⊆ K) :
  (G ⧸ N) ⧸ (K ⧸ N) ≅ G ⧸ K := by
  sorry

-- Proposition 8.11: Second Isomorphism Theorem.
-- ORIGINAL (does not compile).  Mathlib: `QuotientGroup.quotientInfEquivProdNormalQuotient`.
theorem second_isomorphism_theorem (H K : Set G)
  (hs : IsSubgroup H) (hk : IsSubgroup K) (hn : IsNormal H) :
  (H * K : Set G) ⧸ H ≅ K ⧸ (H ⊓ K) := by
  sorry

Example 8.4 (faithful restatement): D_3 ≅ S_3.
-/
theorem dihedral_3_iso_sym_3 : Nonempty (DihedralGroup 3 ≃* Equiv.Perm (Fin 3)) := by
  refine' ⟨ _ ⟩;
  refine' { Equiv.ofBijective ( fun x => if x = DihedralGroup.r 0 then Equiv.refl ( Fin 3 ) else if x = DihedralGroup.r 1 then Equiv.swap 0 1 * Equiv.swap 1 2 else if x = DihedralGroup.r 2 then Equiv.swap 0 2 * Equiv.swap 1 2 else if x = DihedralGroup.sr 0 then Equiv.swap 0 1 else if x = DihedralGroup.sr 1 then Equiv.swap 1 2 else Equiv.swap 0 2 ) ⟨ _, _ ⟩ with .. };
  all_goals simp +decide [ Function.Injective, Function.Surjective ]

/-
Proposition 8.13: Cosets have the same size.
NOTE: rendered with `Nat.card` (the original `Fintype.card` on a `Set` did
not elaborate without a `Fintype` instance).
-/
theorem coset_size_eq (H : Set G) (a : G) :
  Nat.card (LeftCoset H a) = Nat.card H := by
  rw [ Nat.card_congr ];
  symm;
  refine' Equiv.ofBijective ( fun x => ⟨ a * x, _ ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩;
  exact ⟨ x, x.2, rfl ⟩;
  · aesop;
  · rcases x with ⟨ x, hx ⟩;
    rcases hx with ⟨ y, hy, rfl ⟩ ; exact ⟨ ⟨ y, hy ⟩, rfl ⟩

/-
Corollary 8.14: Lagrange's Theorem.
NOTE: rendered with a genuine `Subgroup G` and `Nat.card`.
-/
theorem lagrange_theorem (H : Subgroup G) :
  Nat.card G = Nat.card (G ⧸ H) * Nat.card H := by
  convert Subgroup.card_eq_card_quotient_mul_card_subgroup H using 1

/-
Example 8.15: Order divides group order
-/
theorem order_dvd_card [Fintype G] (g : G) :
  orderOf g ∣ Fintype.card G := by
  exact orderOf_dvd_card

/-
Example 8.16: Prime order groups are cyclic
-/
theorem prime_order_cyclic (p : ℕ) [Fintype G]
  (hp : p.Prime) (hcard : Fintype.card G = p) :
  ∃ g : G, Subgroup.generated {g} = Set.univ := by
  obtain ⟨g, hg⟩ : ∃ g : G, ∀ x : G, x ∈ Subgroup.zpowers g := by
    obtain ⟨g, hg⟩ : ∃ g : G, orderOf g = p := by
      have := Fact.mk hp; exact Exists.imp ( by aesop ) ( exists_prime_orderOf_dvd_card p ( hcard ▸ dvd_rfl ) ) ;
    -- Since $g$ has order $p$, the subgroup generated by $g$ is all of $G$.
    have h_subgroup : Subgroup.zpowers g = ⊤ := by
      refine' Subgroup.eq_top_of_card_eq _ _;
      rw [ Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_zpowers, hg, hcard ];
    exact ⟨ g, fun x => h_subgroup.symm ▸ Subgroup.mem_top x ⟩;
  refine' ⟨ g, _ ⟩;
  convert Set.eq_univ_iff_forall.mpr fun x => Subgroup.mem_closure_singleton.mpr ( hg x );
  convert Subgroup.generated_singleton g;
  simp +decide [ Set.ext_iff, Subgroup.mem_closure_singleton ];
  exact fun x => exists_congr fun n => eq_comm

/-
Example 8.17: Fermat's Little Theorem
-/
theorem fermat_little_theorem (p a : ℕ) (hp : p.Prime) :
  a ^ p ≡ a [MOD p] := by
  haveI := Fact.mk hp; simp +decide [ ← ZMod.natCast_eq_natCast_iff ] ;

/-
-- Proposition 8.18: Characterization of epimorphisms in Ab.
-- ORIGINAL (does not compile: `Coker`, `IsAddGroupHom`, `⊥` on it undefined).
theorem epi_iff_surjective {G H : Type*} [AddCommGroup G] [AddCommGroup H]
  (f : G → H) (hf : IsAddGroupHom f) :
  Surjective f ↔ Coker f = ⊥ := by
  sorry
-/

end IsomorphismTheorems

-- ============================================================================
-- Section 9: Group Actions
-- ============================================================================

section GroupActions

variable {G : Type*} [Group G] {X : Type*}

-- Definition 9.2: Action of group on set
def GroupAction (ρ : G → X → X) : Prop :=
  (∀ a : X, ρ 1 a = a) ∧
  (∀ g h : G, ∀ a : X, ρ (g * h) a = ρ g (ρ h a))

-- Definition 9.7: Orbit
def Orbit (ρ : G → X → X) (a : X) : Set X :=
  {ρ g a | g : G}

-- Definition 9.8: Stabilizer
def Stabilizer (ρ : G → X → X) (a : X) : Set G :=
  {g : G | ρ g a = a}

/-
Lemma 9.7: Stabilizer is subgroup
-/
theorem stabilizer_is_subgroup (ρ : G → X → X) (h : GroupAction ρ) (a : X) :
  IsSubgroup (Stabilizer ρ a) := by
  unfold IsSubgroup Stabilizer;
  cases' h with h1 h2;
  have h_inv : ∀ g : G, ρ g⁻¹ (ρ g a) = a := by
    exact fun g => by rw [ ← h2, inv_mul_cancel, h1 ] ;
  grind

/-
-- Proposition 9.9: Transitive action isomorphic to cosets.
-- ORIGINAL (does not compile: `≅` undefined).
theorem transitive_action_iso_cosets (ρ : G → X → X) (h : GroupAction ρ)
  (X_nonempty : X.Nonempty) (X_transitive : ∀ a b : X, ∃ g : G, ρ g a = b) :
  ∃ (H : Set G), IsSubgroup H ∧
    (Orbit ρ (Classical.choice X_nonempty) ≅ {g : G | g ∈ H}) := by
  sorry

-- Corollary 9.10: Orbit size divides group size.
-- ORIGINAL: `Fintype.card` on the `Set`s `Orbit`/`G` does not elaborate here,
-- and a faithful proof is the orbit-stabilizer theorem for these ad-hoc defs.
-- Mathlib: `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`.
theorem orbit_size_dvd [Fintype G] [Fintype X] (ρ : G → X → X)
  (h : GroupAction ρ) (a : X) :
  Fintype.card (Orbit ρ a) ∣ Fintype.card G := by
  sorry

Proposition 9.12: Stabilizers related by conjugacy.
NOTE: the original right-hand side `{ghg⁻¹ | h ∈ Stabilizer ρ a}` parsed
`ghg⁻¹` as a single unknown identifier; rewritten explicitly.
-/
theorem stabilizer_conjugate (ρ : G → X → X) (h : GroupAction ρ)
  (a : X) (g : G) :
  Stabilizer ρ (ρ g a) = {x : G | ∃ s ∈ Stabilizer ρ a, x = g * s * g⁻¹} := by
  ext x;
  constructor;
  · intro hx
    use g⁻¹ * x * g;
    simp_all +decide [ mul_assoc, Stabilizer ];
    have h_cancel : ρ (g⁻¹ * (x * g)) a = ρ g⁻¹ (ρ x (ρ g a)) := by
      grind +locals;
    have := h.2 g⁻¹ g a; simp_all +decide [ mul_assoc ] ;
    exact this ▸ h.1 a;
  · rintro ⟨ s, hs, rfl ⟩;
    simp_all +decide [ Stabilizer, GroupAction ];
    simp +decide [ ← h.2, hs ]

-- Theorem 9.5: Cayley's Theorem.
-- NOTE: the original quantified over `∃ X : Type*` in an *independent* universe,
-- which cannot be witnessed by `G` itself (universe mismatch) and is not provable
-- for an arbitrary universe.  Cayley's theorem is faithfully captured by letting
-- `G` act on itself (`X = G`, `ρ g x = g * x`), which is what is stated here.
theorem cayley_theorem :
  ∃ (ρ : G → G → G), GroupAction ρ ∧
  (∀ g h : G, g ≠ h → ∃ a : G, ρ g a ≠ ρ h a) := by
  refine ⟨fun g x => g * x, ⟨fun a => one_mul a, fun g h a => mul_assoc g h a⟩, ?_⟩
  intro g h hne
  exact ⟨1, by simpa using hne⟩

end GroupActions

-- ============================================================================
-- Section 10: Group Objects in Categories
-- ============================================================================

section GroupObjects

-- Definition 10.1: Group object in a category (outline).
-- ORIGINAL (does not compile): with `(G : C)`, `G` is a *term* of the type `C`,
-- not a type, so `G → G` is ill-typed.  A faithful definition of a group object
-- in a monoidal/finite-product category is out of scope for this outline file.
/-
class GroupObject (C : Type*) (G : C) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  mul_left_inv : ∀ a : G, mul (inv a) a = one
-/

end GroupObjects

-- ============================================================================
-- EXERCISES
-- ============================================================================

section Exercises

variable {G H : Type*} [Group G] [Group H]

/-
-- Exercise 1.1.
-- ORIGINAL (does not compile: `≅`, `Aut` undefined).  Also false as written:
-- not every group is isomorphic to the automorphism group `Aut X = Equiv.Perm X`
-- of a set.  (The intended statement is Cayley's theorem, `cayley_theorem`.)
theorem every_group_is_iso_of_automorphisms : ∃ (X : Type*),
  G ≅ Aut X := by
  sorry

Exercise 1.3
-/
theorem inv_mul_inv (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  convert mul_inv_rev a b

/-
Exercise 1.4.
NOTE: `CommutativeGroup` is undefined; commutativity is stated directly.
-/
theorem elem_order_two_implies_abelian (h : ∀ g : G, g ^ 2 = 1) :
  ∀ a b : G, a * b = b * a := by
  simp_all +decide [ mul_eq_one_iff_inv_eq, sq ];
  intro a b; have := h ( a * b ) ; have := h a; have := h b; simp_all +decide ;
  rw [ ← inv_inj, h, mul_inv_rev, h, h ]

/-
Exercise 1.9
-/
theorem finite_group_order_2_element [Fintype G] (g : G) :
  (orderOf g = 2) → (2 ∣ Fintype.card G) := by
  exact fun h => h ▸ orderOf_dvd_card

/-
Exercise 1.10
-/
theorem order_power_odd (g : G) (h : Odd (orderOf g)) :
  orderOf (g ^ 2) = orderOf g := by
  rw [ orderOf_pow' ] <;> norm_num [ h ];
  cases h ; aesop

/-
Exercise 1.11
-/
theorem order_conjugate (g h : G) : orderOf (h * g * h⁻¹) = orderOf g := by
  rw [ orderOf_eq_orderOf_iff ];
  simp +decide [ mul_pow, ← mul_assoc ]

/-
-- Exercise 1.12.
-- ORIGINAL (does not compile: `orderOf` is `ℕ`-valued, `∞` is not a valid value;
-- infinite order is `orderOf x = 0` / `¬ IsOfFinOrder x`).  A faithful statement
-- exhibits real 2×2 matrices g, h with |g| = 4, |h| = 3 and gh of infinite order;
-- constructing them is a substantial task left out of scope here.
theorem matrix_example : ∃ (g h : Matrix (Fin 2) (Fin 2) ℝ),
  (orderOf g = 4) ∧ (orderOf h = 3) ∧ (orderOf (g * h) = ∞) := by
  sorry

Exercise 1.14
-/
theorem order_coprime_product (g h : G) (hcomm : Commute g h)
  (hcoprime : Nat.Coprime (orderOf g) (orderOf h)) :
  orderOf (g * h) = orderOf g * orderOf h := by
  convert Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm hcoprime using 1

/-
Exercise 2.2.
NOTE: the original allowed `d = 0`, but no permutation of a finite type has
(multiplicative) order 0; corrected with the hypothesis `0 < d`.
-/
theorem sym_group_has_order_d (n d : ℕ) (hd : d ≤ n) (hd0 : 0 < d) :
  ∃ σ : Equiv.Perm (Fin n), orderOf σ = d := by
  revert n;
  intro n hn
  have h_cycle : ∃ σ : Equiv.Perm (Fin n), orderOf σ = d := by
    have h_embedding : ∃ f : Equiv.Perm (Fin d) →* Equiv.Perm (Fin n), Function.Injective f := by
      refine' ⟨ _, _ ⟩;
      refine' MonoidHom.mk' _ _;
      exact fun f => Equiv.ofBijective ( fun x => if hx : x.val < d then ⟨ f ⟨ x.val, hx ⟩, by linarith [ Fin.is_lt ( f ⟨ x.val, hx ⟩ ) ] ⟩ else x ) ⟨ fun x y hxy => by
        by_cases hx : x.val < d <;> by_cases hy : y.val < d <;> simp_all +decide [ Fin.ext_iff ];
        · have := f.injective ( Fin.ext hxy ) ; aesop;
        · linarith [ Fin.is_lt ( f ⟨ x, hx ⟩ ) ], fun x => by
        use if hx : x.val < d then ⟨ f.symm ⟨ x.val, hx ⟩, by linarith [ Fin.is_lt ( f.symm ⟨ x.val, hx ⟩ ) ] ⟩ else x; aesop; ⟩
      all_goals generalize_proofs at *;
      · intro a b; ext x; aesop;
      · intro f g hfg; ext x; replace hfg := Equiv.congr_fun hfg ⟨ x, by linarith [ Fin.is_lt x ] ⟩ ; aesop;
    obtain ⟨ f, hf ⟩ := h_embedding
    have h_order : ∃ σ : Equiv.Perm (Fin d), orderOf σ = d := by
      have h_cycle : ∃ σ : Equiv.Perm (Fin d), orderOf σ = d := by
        have h_cycle : ∃ σ : Equiv.Perm (ZMod d), orderOf σ = d := by
          use Equiv.addLeft 1;
          rw [ orderOf_eq_iff ] <;> norm_num [ Equiv.Perm.ext_iff ];
          · exact fun m hm₁ hm₂ => by rw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt hm₂ hm₁;
          · grind
        obtain ⟨ σ, hσ ⟩ := h_cycle;
        rcases d with ( _ | _ | d ) <;> simp_all +decide [ ZMod ];
        grind;
      convert h_cycle using 1
    obtain ⟨ σ, hσ ⟩ := h_order
    use f σ
    have h_order_f : orderOf (f σ) = orderOf σ := orderOf_injective f hf σ
    rw [h_order_f, hσ];
  exact h_cycle

/-
-- Exercise 3.3.
-- ORIGINAL (does not compile / false: `(G × H) = G ⊕ H` is an equality of types,
-- which does not hold; the intended statement is that the direct product is the
-- coproduct in the category of abelian groups).
theorem abelian_product_is_coproduct {G H : Type*} [CommGroup G] [CommGroup H] :
  (G × H : Type*) = G ⊕ H := by
  sorry

Exercise 4.3
-/
theorem cyclic_of_order_iff [Fintype G] (n : ℕ) (h : Fintype.card G = n) :
  (∃ g : G, Subgroup.generated {g} = Set.univ) ↔
  (∃ g : G, orderOf g = n) := by
  constructor <;> rintro ⟨ g, hg ⟩ <;> use g;
  · convert Subgroup.card_mul_index ( Subgroup.zpowers g ) using 1;
    · rw [ Subgroup.index_eq_one.mpr ] <;> simp_all +decide [ Subgroup.eq_top_iff' ];
      · rw [ Fintype.card_zpowers ];
      · simp_all +decide [ Set.ext_iff, Subgroup.mem_zpowers_iff ];
        intro x; specialize hg x; rw [ Subgroup.generated_singleton ] at hg; aesop;
    · aesop;
  · have h_subgroup : Subgroup.zpowers g = ⊤ := by
      refine' Subgroup.eq_top_of_card_eq _ _;
      simp +decide [ Nat.card_eq_fintype_card, Fintype.card_zpowers, hg, h ];
    convert congr_arg ( fun s : Subgroup G => s.carrier ) h_subgroup using 1;
    convert Subgroup.generated_singleton g;
    simp +decide [ eq_comm, Set.ext_iff, Subgroup.mem_zpowers_iff ]

/-
Exercise 4.9.
NOTE: `≅` rendered as an additive-group isomorphism `≃+`; `gcd m n = 1`
rendered as `Nat.Coprime m n`.
-/
theorem cyclic_product (m n : ℕ) (h : Nat.Coprime m n) :
  Nonempty (ZMod (m * n) ≃+ ZMod m × ZMod n) := by
  exact ⟨ ( ZMod.chineseRemainder h ).toAddEquiv ⟩

/-
Exercise 4.11
-/
theorem zmodzp_unit_cyclic (p : ℕ) (hp : p.Prime) :
  ∃ g : (ZMod p)ˣ, Subgroup.generated {g} = Set.univ := by
  -- By definition of cyclic groups, the group of units of ZMod p is cyclic.
  have h_cyclic : IsCyclic (ZMod p)ˣ := by
    haveI := Fact.mk hp; infer_instance;
  obtain ⟨ g, hg ⟩ := h_cyclic.exists_generator;
  refine' ⟨ g, _ ⟩;
  ext x;
  obtain ⟨ k, rfl ⟩ := hg x;
  grind +suggestions

/-
Exercise 6.4
-/
theorem cyclic_subgroup_is_cyclic (g : G) :
  ∃ h : G, ∀ x ∈ Subgroup.generated {g}, ∃ n : ℤ, x = h ^ n := by
  refine' ⟨ g, _ ⟩;
  intro x hx
  obtain ⟨n, hn⟩ : ∃ n : ℤ, x ∈ Subgroup.zpowers g := by
    simp_all +decide [ Subgroup.mem_closure_singleton ];
    convert hx ( Subgroup.zpowers g ) ?_ using 1;
    exact ⟨ Set.singleton_subset_iff.mpr ( Subgroup.mem_zpowers g ), ⟨ Subgroup.one_mem _, fun a ha b hb => Subgroup.mul_mem _ ha ( Subgroup.inv_mem _ hb ) ⟩ ⟩;
  exact hn.imp fun n hn => hn.symm

/-
Exercise 6.6
-/
theorem union_subgroup_iff (H K : Set G) (hH : IsSubgroup H) (hK : IsSubgroup K) :
  IsSubgroup (H ∪ K) ↔ (H ⊆ K ∨ K ⊆ H) := by
  constructor <;> intro h;
  · by_contra! h';
    obtain ⟨a, haH, haK⟩ : ∃ a ∈ H, a ∉ K := by
      exact Set.not_subset.mp h'.1
    obtain ⟨b, hbK, hbH⟩ : ∃ b ∈ K, b ∉ H := by
      exact Set.not_subset.mp h'.2
    have hab : a * b ∈ H ∪ K := by
      exact h.mul_mem ( Or.inl haH ) ( Or.inr hbK );
    cases hab <;> have := hH.mul_mem haH ( hH.inv_mem ‹_› ) <;> simp_all +decide [ mul_assoc ];
    · have := hH.mul_mem ( hH.inv_mem haH ) ‹a * b ∈ H›; simp_all +decide [ mul_assoc ] ;
    · have := hK.mul_mem ‹a * b ∈ K› ( hK.inv_mem hbK ) ; simp_all +decide [ mul_assoc ] ;
  · cases' h with h h <;> simp_all +decide [ IsSubgroup ]; all_goals grind

/-
-- Exercise 6.9.
-- ORIGINAL (does not compile: `Fintype.card H < ∞` is not well-typed, and mixes
-- `Subgroup ℚ` with the `Set`-based `Subgroup.generated`).  A faithful statement
-- would say: every finitely generated subgroup of ℚ is cyclic.
theorem fingen_subgroup_of_rationals (H : Subgroup ℚ) (hfin : Fintype.card H < ∞) :
  ∃ n : ℕ, H = Subgroup.generated {n⁻¹} := by
  sorry

-- Exercise 6.12.
-- ORIGINAL.  As with Proposition 6.9, the `Subgroup.generated`/`IsSubgroup`
-- machinery here is *multiplicative* and cannot be applied to the additive group
-- `ℤ` (`Group ℤ` does not exist); a faithful statement would use additive
-- subgroups.
theorem gcd_of_generated_integers (m n : ℕ) :
  Subgroup.generated ({(m : ℤ), (n : ℤ)} : Set ℤ) =
  Subgroup.generated {(Nat.gcd m n : ℤ)} := by
  sorry

-- Exercise 7.1.
-- ORIGINAL (does not compile: `Subgroup.card`, `Subgroup.bot` undefined and the
-- statement is a malformed placeholder about the subgroup lattice of S_3).
theorem s3_subgroups_and_normality : ∃ (N : Fintype (Subgroup (Equiv.Perm (Fin 3)))),
  Fintype.card N = 6 ∧ ∃ k : ℕ, k < 6 ∧ (k ≠ Subgroup.card (Subgroup.bot _)) := by
  sorry

-- Exercise 7.4.
-- ORIGINAL: a vacuous placeholder (`True` under trivial data); nothing to prove.
theorem quotient_equivalence_relation (h : True) :
  ∃ (F : FreeAbelianGroup (Fin 1)) (R : Set F)
    (hcompat : ∀ a b ∈ R, True),
  True := by
  sorry

Exercise 7.11.
NOTE: `IsNormal` here is the ad-hoc conjugation-closed predicate defined above.
The *set* of single commutators is closed under conjugation, which is exactly
what this predicate asserts.
-/
theorem commutator_subgroup_normal :
  IsNormal {x : G | ∃ g h : G, x = ⁅g, h⁆} := by
  intro g n hn
  obtain ⟨g', h', hn'⟩ := hn
  use g * g' * g⁻¹, g * h' * g⁻¹
  simp [hn', commutatorElement_def];
  group

/-
Exercise 8.2.
NOTE: original `(⊤ : Subgroup G).index H` was malformed; `Subgroup.index`
takes a single subgroup, so this is `H.index = 2`.
-/
theorem index_two_is_normal (H : Subgroup G)
  (hindex : H.index = 2) :
  H.Normal := by
  convert Subgroup.normal_of_index_eq_two hindex

/-
-- Exercise 8.5.
-- ORIGINAL (does not compile: `≅`, `Dihedral` undefined).  Faithful statement:
-- a group generated by two involutions a, b with |ab| = 6 is dihedral of order
-- 12; expressing this with the ad-hoc `Subgroup.generated` and a `≃*` to
-- `DihedralGroup 6` is out of scope here.
theorem generated_by_order_2_generators (a b : G)
  (ha : orderOf a = 2) (hb : orderOf b = 2)
  (hab : orderOf (a * b) = 2 * 3) :
  ∃ n : ℕ, Subgroup.generated {a, b} ≅ Dihedral n := by
  sorry

Exercise 8.13
-/
theorem odd_order_all_squares [Fintype G] (h : Odd (Fintype.card G)) :
  ∀ g : G, ∃ k : G, g = k ^ 2 := by
  intro g
  obtain ⟨k, hk⟩ : ∃ k : G, g = k ^ (Fintype.card G + 1) := by
    have h_order : g ^ (Fintype.card G) = 1 := by
      rw [ pow_card_eq_one ];
    exact ⟨ g, by rw [ pow_succ', h_order, mul_one ] ⟩;
  exact ⟨ k ^ ( ( Fintype.card G + 1 ) / 2 ), by rw [ hk, ← pow_mul, Nat.div_mul_cancel ( even_iff_two_dvd.mp ( by simpa [ parity_simps ] using h ) ) ] ⟩

/-
Exercise 8.14
-/
theorem power_surjective [Fintype G] (k : ℕ)
  (h : Nat.Coprime k (Fintype.card G)) :
  Function.Surjective (fun g : G => g ^ k) := by
  -- By definition of coprimality, there exists an integer $m$ such that $km \equiv 1 \pmod{|G|}$.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k * m ≡ 1 [MOD Fintype.card G] := by
    have := Nat.exists_mul_mod_eq_one_of_coprime h;
    rcases n : Fintype.card G with ( _ | _ | n ) <;> simp_all +decide [ Nat.ModEq, Nat.mod_one ];
    exact ⟨ this.choose, this.choose_spec.2 ⟩;
  intro g
  use g ^ m;
  simp +decide [ ← pow_mul, ← pow_add, hm ];
  rw [ mul_comm, ← Nat.mod_add_div ( k * m ) ( Fintype.card G ), hm ] ; simp +decide [ pow_add, pow_mul, pow_card_eq_one ]

/-
Exercise 8.17
-/
theorem abelian_prime_order_element {A : Type*} [CommGroup A] [Fintype A] (p : ℕ)
  (hp : p.Prime) (hdiv : p ∣ Fintype.card A) :
  ∃ g : A, orderOf g = p := by
  have := Fact.mk hp;
  convert exists_prime_orderOf_dvd_card p hdiv

/-
Exercise 8.20.
NOTE: rendered with `Nat.card`.
-/
theorem abelian_subgroup_of_div_order {A : Type*} [CommGroup A] [Fintype A] (d : ℕ)
  (hdiv : d ∣ Fintype.card A) :
  ∃ H : Subgroup A, Nat.card H = d := by
  revert d;
  -- Let $p$ be a prime dividing $d$.
  intro d hd
  induction' d using Nat.strong_induction_on with d ih generalizing A;
  by_cases hd1 : d = 1;
  · refine' ⟨ ⊥, _ ⟩ ; simp +decide [ hd1 ];
  · -- Let $p$ be a prime dividing $d$. By Cauchy's theorem, there exists an element $g$ of order $p$ in $A$.
    obtain ⟨p, hp_prime, hp_div⟩ : ∃ p, Nat.Prime p ∧ p ∣ d := by
      exact Nat.exists_prime_and_dvd hd1
    obtain ⟨g, hg⟩ : ∃ g : A, orderOf g = p := by
      haveI := Fact.mk hp_prime; exact Exists.imp ( by aesop ) ( exists_prime_orderOf_dvd_card p ( dvd_trans hp_div hd ) ) ;
    -- Let $B = A / \langle g \rangle$.
    set B := A ⧸ Subgroup.zpowers g;
    -- By the induction hypothesis, there exists a subgroup $H'$ of $B$ with order $d/p$.
    obtain ⟨H', hH'⟩ : ∃ H' : Subgroup B, Nat.card H' = d / p := by
      apply ih (d / p);
      · exact Nat.div_lt_self ( Nat.pos_of_dvd_of_pos hd ( Fintype.card_pos ) ) hp_prime.one_lt;
      · have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( Subgroup.zpowers g );
        simp_all +decide [ Nat.card_eq_fintype_card, Fintype.card_zpowers ];
        exact Nat.dvd_of_mul_dvd_mul_right hp_prime.pos ( by convert hd using 1; rw [ Nat.div_mul_cancel hp_div ] );
    -- Let $H$ be the preimage of $H'$ under the quotient map $A \to B$.
    use Subgroup.comap (QuotientGroup.mk' (Subgroup.zpowers g)) H';
    have := Subgroup.card_mul_index ( Subgroup.comap ( QuotientGroup.mk' ( Subgroup.zpowers g ) ) H' ) ; simp_all +decide [ Subgroup.index_comap ] ;
    have := Subgroup.card_mul_index H'; simp_all +decide [ Subgroup.index ] ;
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( Subgroup.zpowers g ) ; simp_all +decide [ Nat.card_eq_fintype_card ] ;
    simp_all +decide [ Fintype.card_zpowers ];
    nlinarith [ Nat.div_mul_cancel hp_div, Nat.pos_of_ne_zero ( show Fintype.card ( A ⧸ Subgroup.zpowers g ) ≠ 0 from Fintype.card_ne_zero ) ]

/-
-- Exercise 8.21.
-- ORIGINAL (does not compile: `⁻¹` applied to `Fintype.card` and to a `Set`,
-- and `Fintype.card` on `Set`s without instances).  The intended identity is
-- |H| · |K| = |HK| · |H ∩ K|.
theorem coset_bijection (H K : Subgroup G) :
  Fintype.card (H : Set G) * Fintype.card ((H ⊓ K : Subgroup G) : Set G)⁻¹
  = Fintype.card ((H * K : Set G)) * Fintype.card (K : Set G) := by
  sorry

Exercise 9.5
-/
theorem left_mult_action_free (g : G) : g ≠ 1 →
  ∃ a : G, g * a ≠ a := by
  exact fun h => ⟨ 1, by simpa using h ⟩

/-
-- Exercise 9.11.
-- ORIGINAL, and FALSE as stated: a subgroup of prime index need not be normal
-- (e.g. a subgroup of order 2 in S_3 has index 3, which is prime, but is not
-- normal).  The correct statement requires the index to be the *smallest* prime
-- dividing |G|.
theorem prime_index_subgroup_normal (H : Subgroup G) [Fintype G]
  (hp : (Fintype.card G / Fintype.card H).Prime) :
  H.Normal := by
  sorry
-/

/-
-- Exercise 10.2.
-- ORIGINAL (does not compile: `GroupObject` expects a category `C` and an object
-- `G : C`; `GroupObject Set G` is ill-typed).  A faithful statement would say
-- that every group is a group object in the category of sets.
theorem groups_are_group_objects_in_set : ∀ (G : Type*) [Group G],
  GroupObject Set G := by
  sorry
-/

end Exercises

end GroupTheory

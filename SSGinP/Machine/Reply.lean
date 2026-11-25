module

public import SSGinP.Theory.Main
public import SSGinP.Search.Search
public import SSGinP.Machine.Decode
public import Mathlib.Data.Nat.Size

@[expose] public section

/-!
# SSGinP.Machine.Reply: the mathematical reply function of the single-call reduction

Shared by the machine (which computes it) and by `single_call_correct`.

Goods `Fin (2n+1)`: `dummy n = 0` (the anchor), `upG j = 1 + j`, `downG j = 1 + n + j` (from SSGinP.Search.Search).
For a price vector `q`, `lo j = δ w_j (q (upG j) - q 0)`, `hi j = -(δ w_j (q (downG j) - q 0))`, `w = SSG.wt G`.
Reply at good `g`: dummy: `θ < lo start`; `upG j`: `lo j < F(lo) j`; `downG j`: `F(hi) j < hi j`.
The threshold `θ` and the step `δ` are parameters; the two instantiations (with `D = 3^n` bounding the
denominators of the values, so a value differs from 1/2 by at least 1/(2D) unless equal):
* `thetaGe n = 1/2 - 1/(4 9^n)`: `v ≥ 1/2 ↔ θ < v` (the paper's problem),
* `thetaGt n = 1/2 + 1/(4 9^n)`: `v > 1/2 ↔ θ < v` (Condon's variant),
with gap `Delta n = 1/(4 9^n)`, `γ = gam n = 1/(4 3^n)`, `T = 4 3^n`, `δ = rDelta n = 1/(64 27^n)`,
`K = 64 27^n`, `R = rR n = 2K`.  (`T γ = 1`, `2 δ (T+1) ≤ 10/(64 9^n) < Delta n`, `T ≤ K`, `1/δ = K`.)
The reply on a word is `false` unless the word is a `priceQuery` and the game is well formed and stopping
(peeling succeeds): then the negative hypothesis is consistent and the sign machine outputs `false`.
-/

namespace SSG28Reply

open SSG SSG28Search OAI.Optimization.LinearProgramming.OracleSpec

variable {n : ℕ}

def Delta (n : ℕ) : ℚ := 1 / (4 * 9 ^ n)
def thetaGe (n : ℕ) : ℚ := 1 / 2 - Delta n
def thetaGt (n : ℕ) : ℚ := 1 / 2 + Delta n
def rDelta (n : ℕ) : ℚ := 1 / (64 * 27 ^ n)
def rK (n : ℕ) : ℕ := 64 * 27 ^ n
def rT (n : ℕ) : ℕ := 4 * 3 ^ n
def rR (n : ℕ) : ℕ := 2 * rK n

def lo (G : Game n) (δ : ℚ) (q : Fin (2*n+1) → ℚ) (j : Fin n) : ℚ :=
  δ * wt G j * (q (upG j) - q (dummy n))
def hi (G : Game n) (δ : ℚ) (q : Fin (2*n+1) → ℚ) (j : Fin n) : ℚ :=
  -(δ * wt G j * (q (downG j) - q (dummy n)))

/-- the reply at good `g` and prices `q`. -/
def replyGood (G : Game n) (θ δ : ℚ) (g : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ) : Bool :=
  if h0 : g.val = 0 then decide (θ < lo G δ q G.startNode)
  else if h : g.val ≤ n then
    decide (lo G δ q ⟨g.val - 1, by omega⟩ < F G (lo G δ q) ⟨g.val - 1, by omega⟩)
  else decide (F G (hi G δ q) ⟨g.val - 1 - n, by omega⟩ < hi G δ q ⟨g.val - 1 - n, by omega⟩)

theorem replyGood_dummy (G : Game n) (θ δ : ℚ) (q) :
    replyGood G θ δ (dummy n) q = decide (θ < lo G δ q G.startNode) := by
  simp [replyGood, dummy]

theorem replyGood_up (G : Game n) (θ δ : ℚ) (j : Fin n) (q) :
    replyGood G θ δ (upG j) q = decide (lo G δ q j < F G (lo G δ q) j) := by
  unfold replyGood
  rw [dif_neg (show (upG j).val ≠ 0 by simp [upG]), dif_pos (show (upG j).val ≤ n by simp [upG]; omega)]
  have e : ∀ h, (⟨(upG j).val - 1, h⟩ : Fin n) = j := fun h => Fin.ext (by simp [upG])
  rw [e]

theorem replyGood_down (G : Game n) (θ δ : ℚ) (j : Fin n) (q) :
    replyGood G θ δ (downG j) q = decide (F G (hi G δ q) j < hi G δ q j) := by
  unfold replyGood
  rw [dif_neg (show (downG j).val ≠ 0 by simp [downG]), dif_neg (show ¬ (downG j).val ≤ n by simp [downG]; omega)]
  have e : ∀ h, (⟨(downG j).val - 1 - n, h⟩ : Fin n) = j := fun h => Fin.ext (by simp [downG]; omega)
  rw [e]

/-- the precheck: well formed (one terminal of each kind) and stopping (peeling succeeds). -/
def okGame (G : Game n) : Bool := decide (WellFormed G) && peelAll G

/-! ### `priceQuery` is injective -/

theorem frame_append_inj : ∀ (a b r s : Word), frame a ++ r = frame b ++ s → a = b ∧ r = s
  | [], [], r, s, h => by simpa [frame] using h
  | [], _ :: _, r, s, h => by simp [frame] at h
  | _ :: _, [], r, s, h => by simp [frame] at h
  | x :: a, y :: b, r, s, h => by
    simp only [frame, List.foldr_cons, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨hxy, h⟩ := h
    have := frame_append_inj a b r s (by simpa [frame] using h)
    exact ⟨by rw [hxy, this.1], this.2⟩

theorem bits_inj {a b : ℕ} (h : a.bits = b.bits) : a = b := by
  have key : ∀ m : ℕ, ∀ a b : ℕ, a.bits.length ≤ m → a.bits = b.bits → a = b := by
    intro m
    induction m with
    | zero =>
      intro a b ha h
      have ha0 : a.size = 0 := by rw [← Nat.size_eq_bits_len]; omega
      have hb0 : b.size = 0 := by rw [← Nat.size_eq_bits_len, ← h, Nat.size_eq_bits_len]; exact ha0
      rw [Nat.size_eq_zero.mp ha0, Nat.size_eq_zero.mp hb0]
    | succ m ih =>
      intro a b ha h
      have hd : a.div2 = b.div2 := ih _ _ (by rw [Nat.div2_bits_eq_tail]; simp; omega)
        (by rw [Nat.div2_bits_eq_tail, Nat.div2_bits_eq_tail, h])
      have ho : a.bodd = b.bodd := by rw [Nat.bodd_eq_bits_head, Nat.bodd_eq_bits_head, h]
      rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b, hd, ho]
  exact key _ a b le_rfl h

theorem encodeNat_append_inj {a b : ℕ} {r s : Word} (h : encodeNat a ++ r = encodeNat b ++ s) : a = b ∧ r = s := by
  obtain ⟨h1, h2⟩ := frame_append_inj _ _ _ _ h
  exact ⟨bits_inj h1, h2⟩

theorem encodeRat_append_inj {x y : ℚ} {r s : Word} (h : encodeRat x ++ r = encodeRat y ++ s) : x = y ∧ r = s := by
  simp only [encodeRat, List.cons_append, List.cons.injEq, List.append_assoc] at h
  obtain ⟨hs, h⟩ := h
  obtain ⟨hn, h⟩ := encodeNat_append_inj h
  obtain ⟨hd, h⟩ := encodeNat_append_inj h
  refine ⟨?_, h⟩
  have hnum : x.num = y.num := by
    have hs' : (x.num < 0) ↔ (y.num < 0) := by simpa using hs
    rcases lt_or_ge x.num 0 with hx | hx
    · have hy := hs'.mp hx; omega
    · have hy : 0 ≤ y.num := by by_contra hy; exact absurd (hs'.mpr (by omega)) (by omega)
      omega
  exact Rat.ext hnum hd

theorem flatMap_encodeRat_inj : ∀ (l l' : List ℚ), l.length = l'.length →
    l.flatMap encodeRat = l'.flatMap encodeRat → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: l, y :: l', hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨hxy, h⟩ := encodeRat_append_inj h
    rw [hxy, flatMap_encodeRat_inj l l' (by simpa using hl) h]

theorem priceQuery_inj {N : ℕ} {i i' : Fin N} {q q' : Fin N → ℚ} (h : priceQuery i q = priceQuery i' q') :
    i = i' ∧ q = q' := by
  unfold priceQuery at h
  obtain ⟨hi, h⟩ := encodeNat_append_inj h
  refine ⟨Fin.ext hi, ?_⟩
  have := flatMap_encodeRat_inj _ _ (by simp) h
  exact List.ofFn_injective this

/-! ### the reply on words -/

open Classical in
/-- **the reply on a query word** (`false` on words that are not price queries). -/
noncomputable def ssgReply (G : Game n) (θ δ : ℚ) (w : Word) : Bool :=
  if h : ∃ x : Fin (2*n+1) × (Fin (2*n+1) → ℚ), w = priceQuery x.1 x.2 then
    okGame G && replyGood G θ δ h.choose.1 h.choose.2
  else false

theorem ssgReply_priceQuery (G : Game n) (θ δ : ℚ) (i : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ) :
    ssgReply G θ δ (priceQuery i q) = (okGame G && replyGood G θ δ i q) := by
  have hex : ∃ x : Fin (2*n+1) × (Fin (2*n+1) → ℚ), priceQuery i q = priceQuery x.1 x.2 := ⟨(i, q), rfl⟩
  unfold ssgReply
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := priceQuery_inj hex.choose_spec
  rw [← h1, ← h2]

/-! ### the machine-level functions (on the input word) -/

/-- the reply of the oracle for the input word `x` and the query word `w`, threshold family `θ`. -/
noncomputable def replyW (θ : ℕ → ℚ) (x w : Word) : Bool :=
  match SSG28Decode.decode x with
  | some ⟨n, G⟩ => ssgReply G (θ n) (rDelta n) w
  | none => false

/-- the driver: the public input of the sign-recovery machine. -/
def driverW (x : Word) : Word :=
  match SSG28Decode.decode x with
  | some ⟨n, _⟩ => priceInput (rR n) (dummy n)
  | none => priceInput (N := 1) 1 0

end SSG28Reply

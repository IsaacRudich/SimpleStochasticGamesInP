module

public import SSGinP.GameFacts
public import SSGinP.Machine.Decode
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# SSGinP.Bridge.EncodeDecode: the Challenge encoding is read back by the internal decoder

* `SSG.encode_length_proved : (encode ⟨n, G⟩).length = 10 * n ^ 2`;
* `SSGinP.decode_encode : SSG28Decode.decode (SSG.encode x).reverse = some x` (the decoder reads `w.reverse`);
* `SSG.encode_injective_proved : Function.Injective encode`.

`Game 0` is empty (a game has a start node in `Fin 0`), so there is no instance with `n = 0` and all three
statements hold without any side condition (`SSGinP.game_pos`).
-/

namespace SSGinP

open SSG SSG28Decode

/-! ### One-hot lists over a range -/

section OneHotLemmas

theorem count_map_range (f : ℕ → Bool) :
    ∀ N, ((List.range N).map f).count true = ((Finset.range N).filter (fun i => f i = true)).card
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.map_append, List.count_append, count_map_range f N, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : f N = true
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · rw [if_neg h]
      simp [h]

theorem oneHot_iff (f : ℕ → Bool) (N : ℕ) :
    OneHot ((List.range N).map f) ↔ ∃ i < N, f i = true ∧ ∀ j < N, f j = true → j = i := by
  unfold OneHot
  rw [count_map_range, Finset.card_eq_one]
  constructor
  · rintro ⟨a, ha⟩
    have hm : a ∈ (Finset.range N).filter (fun i => f i = true) := by rw [ha]; simp
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    refine ⟨a, hm.1, hm.2, fun j hj hfj => ?_⟩
    have : j ∈ (Finset.range N).filter (fun i => f i = true) := by simp [hj, hfj]
    rw [ha] at this; simpa using this
  · rintro ⟨i, hi, hfi, huniq⟩
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hfj⟩; exact huniq j hj hfj
    · rintro rfl; exact ⟨hi, hfi⟩

theorem idxOf_true_eq : ∀ (l : List Bool) (i : ℕ), l[i]? = some true → (∀ j < i, l[j]? ≠ some true) →
    l.idxOf true = i
  | [], i, h, _ => by simp at h
  | b :: l, 0, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp
  | b :: l, i + 1, h, hj => by
    have hb : b = false := by
      have := hj 0 (Nat.succ_pos _)
      simp only [List.getElem?_cons_zero, ne_eq, Option.some.injEq] at this
      simpa using this
    subst hb
    rw [List.idxOf_cons_ne _ (by decide)]
    congr 1
    exact idxOf_true_eq l i (by simpa using h) (fun j hji => by simpa using hj (j + 1) (by omega))

/-- in a one-hot list over a range, the position is the unique index set. -/
theorem pos_eq_iff (f : ℕ → Bool) (N : ℕ) (h : OneHot ((List.range N).map f)) (j : ℕ) (hj : j < N) :
    pos ((List.range N).map f) = j ↔ f j = true := by
  obtain ⟨i, hi, hfi, huniq⟩ := (oneHot_iff f N).mp h
  have hpos : pos ((List.range N).map f) = i := by
    unfold pos
    refine idxOf_true_eq _ i (by simp [hi, hfi]) (fun j' hj' => ?_)
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, ne_eq, Option.some.injEq]
    intro hf; have := huniq j' (by omega) hf; omega
  rw [hpos]
  constructor
  · rintro rfl; exact hfi
  · intro hf; exact (huniq j hj hf).symm

end OneHotLemmas

/-- the indicator row of a position `a < N` is one-hot. -/
theorem oneHot_indicator (N a : ℕ) (ha : a < N) : OneHot ((List.range N).map (fun j => decide (a = j))) :=
  (oneHot_iff _ N).mpr ⟨a, ha, by simp, fun j _ hj => (of_decide_eq_true hj).symm⟩

/-- the position read from the indicator row of `a < N` is `a`. -/
theorem pos_indicator (N a : ℕ) (ha : a < N) : pos ((List.range N).map (fun j => decide (a = j))) = a :=
  (pos_eq_iff _ N (oneHot_indicator N a ha) a ha).mpr (by simp)

/-! ### Words made of blocks of one length -/

/-- entry `i * c + k` of a concatenation of blocks of length `c` is entry `k` of block `i`. -/
theorem getElem?_flatMap_uniform {α β : Type} (f : α → List β) (c : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = c) → ∀ (i : ℕ) (hi : i < l.length) (k : ℕ), k < c →
      (l.flatMap f)[i * c + k]? = (f l[i])[k]?
  | [], _, i, hi, _, _ => by simp at hi
  | a :: l, h, 0, _, k, hk => by
    have ha : (f a).length = c := h a (by simp)
    simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
    exact List.getElem?_append_left (by omega)
  | a :: l, h, i + 1, hi, k, hk => by
    have ha : (f a).length = c := h a (by simp)
    have hi' : i < l.length := by simpa using hi
    have := getElem?_flatMap_uniform f c l (fun b hb => h b (by simp [hb])) i hi' k hk
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [List.getElem?_append_right (by rw [ha, Nat.succ_mul]; omega), ← this]
    congr 1
    rw [ha, Nat.succ_mul]; omega

/-! ### The length -/

theorem bits_length (t : NodeType) : t.bits.length = 5 := by cases t <;> rfl

theorem pairBits_length {n : ℕ} (G : Game n) (u v : Fin n) : (pairBits G u v).length = 10 := by
  simp [pairBits, bits_length]

theorem row_length {n : ℕ} (G : Game n) (u : Fin n) :
    ((List.finRange n).flatMap fun v => pairBits G u v).length = n * 10 := by
  simp [List.length_flatMap, pairBits_length]

theorem encode_length' {n : ℕ} (G : Game n) : (encode ⟨n, G⟩).length = n * n * 10 := by
  simp [encode, List.length_flatMap, pairBits_length, Nat.mul_assoc]

/-- there is no game on `0` nodes. -/
theorem game_pos {n : ℕ} (G : Game n) : 1 ≤ n := by
  rcases n with _ | n
  · exact G.startNode.elim0
  · omega

/-! ### Reading the word -/

/-- **the index formula**: bit `(i * n + j) * 10 + k` of the word is bit `k` of the block of `(i, j)`. -/
theorem encode_getElem? {n : ℕ} (G : Game n) (i j : Fin n) (k : ℕ) (hk : k < 10) :
    (encode ⟨n, G⟩)[(i.val * n + j.val) * 10 + k]? = (pairBits G i j)[k]? := by
  have h1 := getElem?_flatMap_uniform (fun u => (List.finRange n).flatMap fun v => pairBits G u v) (n * 10)
    (List.finRange n) (fun u _ => row_length G u) i.val (by simp) (j.val * 10 + k) (by have := j.2; omega)
  have h2 := getElem?_flatMap_uniform (fun v => pairBits G i v) 10
    (List.finRange n) (fun v _ => pairBits_length G i v) j.val (by simp) k hk
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta] at h1 h2
  rw [← h2, ← h1, encode]
  congr 1
  ring

theorem nOf_encode {n : ℕ} (G : Game n) : nOf (encode ⟨n, G⟩) = n := by
  unfold nOf
  rw [encode_length', Nat.mul_div_cancel _ (by norm_num), ← pow_two]
  exact Nat.sqrt_eq' _

theorem bit_encode {n : ℕ} (G : Game n) (i j : Fin n) (k : ℕ) (hk : k < 10) :
    bit (encode ⟨n, G⟩) i.val j.val k = (pairBits G i j).getD k false := by
  unfold bit
  rw [nOf_encode, List.getD_eq_getElem?_getD, encode_getElem? G i j k hk, List.getD_eq_getElem?_getD]

theorem typeOf_pos_bits (t : NodeType) : typeOf (pos t.bits) = t := by cases t <;> rfl

theorem oneHot_bits (t : NodeType) : OneHot t.bits := by cases t <;> rfl

theorem typeBits_encode {n : ℕ} (G : Game n) (i : Fin n) :
    typeBits (encode ⟨n, G⟩) i.val = (G.nodeType i).bits := by
  have hn := game_pos G
  have hb : ∀ k < 5, bit (encode ⟨n, G⟩) i.val 0 k = (pairBits G i ⟨0, hn⟩).getD k false :=
    fun k hk => bit_encode G i ⟨0, hn⟩ k (by omega)
  unfold typeBits
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil,
    hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num), hb 4 (by norm_num)]
  unfold pairBits
  cases G.nodeType i <;> rfl

theorem childRow_encode_false {n : ℕ} (G : Game n) (i : Fin n) :
    childRow (encode ⟨n, G⟩) i.val false = (List.range n).map (fun j => decide ((G.childJ i).val = j)) := by
  unfold childRow
  rw [nOf_encode]
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < n := List.mem_range.mp hj
  have := bit_encode G i ⟨j, hj'⟩ 6 (by norm_num)
  simp only [Bool.false_eq_true, if_false]
  rw [this]
  unfold pairBits
  cases G.nodeType i <;> simp [NodeType.bits, Fin.ext_iff]

theorem childRow_encode_true {n : ℕ} (G : Game n) (i : Fin n) :
    childRow (encode ⟨n, G⟩) i.val true = (List.range n).map (fun j => decide ((G.childK i).val = j)) := by
  unfold childRow
  rw [nOf_encode]
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < n := List.mem_range.mp hj
  have := bit_encode G i ⟨j, hj'⟩ 7 (by norm_num)
  simp only [if_true]
  rw [this]
  unfold pairBits
  cases G.nodeType i <;> simp [NodeType.bits, Fin.ext_iff]

theorem startCol_encode {n : ℕ} (G : Game n) :
    startCol (encode ⟨n, G⟩) = (List.range n).map (fun i => decide (G.startNode.val = i)) := by
  have hn := game_pos G
  unfold startCol
  rw [nOf_encode]
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < n := List.mem_range.mp hi
  have := bit_encode G ⟨i, hi'⟩ ⟨0, hn⟩ 5 (by norm_num)
  simp only at this
  rw [this]
  unfold pairBits
  cases G.nodeType ⟨i, hi'⟩ <;> simp [NodeType.bits, Fin.ext_iff]

/-- the word of a game has the shape the decoder asks for. -/
theorem validL_encode {n : ℕ} (G : Game n) : ValidL (encode ⟨n, G⟩) := by
  refine ⟨by rw [nOf_encode]; exact game_pos G, by rw [nOf_encode, encode_length'], fun i hi => ?_, ?_⟩
  · rw [nOf_encode] at hi
    have h0 := typeBits_encode G ⟨i, hi⟩
    have h1 := childRow_encode_false G ⟨i, hi⟩
    have h2 := childRow_encode_true G ⟨i, hi⟩
    simp only at h0 h1 h2
    rw [h0, h1, h2]
    exact ⟨oneHot_bits _, oneHot_indicator n _ (G.childJ _).2, oneHot_indicator n _ (G.childK _).2⟩
  · rw [startCol_encode]
    exact oneHot_indicator n _ G.startNode.2

/-- a decoded game equals `G` as soon as the number of nodes and the four fields agree. -/
theorem sigma_gameOf_eq (l : List Bool) (h : ValidL l) (n : ℕ) (G : Game n) (hn : nOf l = n)
    (ht : ∀ i : Fin n, typeOf (pos (typeBits l i.val)) = G.nodeType i)
    (hj : ∀ i : Fin n, pos (childRow l i.val false) = (G.childJ i).val)
    (hk : ∀ i : Fin n, pos (childRow l i.val true) = (G.childK i).val)
    (hs : pos (startCol l) = G.startNode.val) :
    (⟨nOf l, gameOf l h⟩ : Σ n, Game n) = ⟨n, G⟩ := by
  subst hn
  congr 1
  rcases G with ⟨nt, cj, ck, s⟩
  simp only [gameOf, Game.mk.injEq]
  refine ⟨funext fun i => ht i, funext fun i => Fin.ext (hj i), funext fun i => Fin.ext (hk i), Fin.ext hs⟩

/-- **the round trip**: the decoder (which reads its argument reversed) returns the game from the reversed word. -/
theorem decode_encode (x : Σ n, Game n) : SSG28Decode.decode (encode x).reverse = some x := by
  obtain ⟨n, G⟩ := x
  unfold decode
  rw [List.reverse_reverse, dif_pos (validL_encode G)]
  congr 1
  refine sigma_gameOf_eq _ _ n G (nOf_encode G) (fun i => ?_) (fun i => ?_) (fun i => ?_) ?_
  · rw [typeBits_encode, typeOf_pos_bits]
  · rw [childRow_encode_false]; exact pos_indicator n _ (G.childJ i).2
  · rw [childRow_encode_true]; exact pos_indicator n _ (G.childK i).2
  · rw [startCol_encode]; exact pos_indicator n _ G.startNode.2

end SSGinP

namespace SSG

variable {n : Nat}

/-- the word of a game on `n` nodes has length exactly `10 n²`. -/
theorem encode_length_proved (G : Game n) : (encode ⟨n, G⟩).length = 10 * n ^ 2 := by
  rw [SSGinP.encode_length']; ring

/-- the word determines the game: different games have different words. -/
theorem encode_injective_proved : Function.Injective encode := by
  intro x y h
  have hx := SSGinP.decode_encode x
  rw [h, SSGinP.decode_encode y] at hx
  exact (Option.some.inj hx).symm

end SSG

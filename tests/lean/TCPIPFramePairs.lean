import TCPIPFrameCatalog
open Approved FormalSpecAgent FormalSpecAgent.TypedIR FormalSpecAgent.TypedMachine
open FormalSpecAgent.GuardDiscriminators FormalSpecAgent.TimedObligations
namespace TCPIPFramePairs
private theorem impossible {a b : Bool} (h : a = true → b = true → False) :
    a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all

/-- Extract a necessary conjunct. A path ends at the first node that is not a conjunction. -/
private def conjunctAt : List Char → Expr .boolean → Expr .boolean
  | direction :: rest, .boolAnd a b => conjunctAt rest (if direction == 'L' then a else b)
  | _, guard => guard

private theorem evalConjunct (s : Snapshot) (f : Values) (path : List Char)
    (guard : Expr .boolean) (h : TypedMachine.eval s f guard = true) :
    TypedMachine.eval s f (conjunctAt path guard) = true := by
  fun_induction conjunctAt path guard with
  | case1 direction rest a b ih =>
    change (TypedMachine.eval s f a && TypedMachine.eval s f b) = true at h
    simp only [Bool.and_eq_true] at h
    apply ih
    split
    · exact h.1
    · exact h.2
  | _ => exact h

private theorem leaf (s : Snapshot) (f : Values) (path : String) (rule : Rule)
    (atom : Expr .boolean) (found : conjunctAt path.toList rule.guard = atom)
    (h : TypedMachine.eval s f rule.guard = true) : TypedMachine.eval s f atom = true :=
  found ▸ evalConjunct s f path.toList rule.guard h

private theorem complement (s : Snapshot) (f : Values) (g : Expr .boolean)
    (positive : TypedMachine.eval s f g = true)
    (negative : TypedMachine.eval s f (.boolNot g) = true) : False := by
  change (!TypedMachine.eval s f g) = true at negative
  simp [positive] at negative

private theorem conjunctComplement (s : Snapshot) (f : Values) (a b : Expr .boolean)
    (positiveA : TypedMachine.eval s f a = true)
    (positiveB : TypedMachine.eval s f b = true)
    (negative : TypedMachine.eval s f (.boolNot (.boolAnd (.boolAnd (.literal .boolean true) a) b)) = true) :
    False := by
  change (!((true && TypedMachine.eval s f a) && TypedMachine.eval s f b)) = true at negative
  simp only [positiveA, positiveB] at negative
  contradiction
private theorem seq_add_one_ne (a : ValueOps.Seq32) : ValueOps.seqAdd a 1 ≠ a := by
  intro same
  have values := congrArg Fin.val same
  change (((a.val : Int) + 1) % 4294967296).toNat % 4294967296 = a.val at values
  have nonnegative : 0 ≤ ((a.val : Int) + 1) % 4294967296 := Int.emod_nonneg _ (by decide)
  have below : ((a.val : Int) + 1) % 4294967296 < 4294967296 := Int.emod_lt_of_pos _ (by decide)
  have original := a.isLt
  rw [Nat.mod_eq_of_lt (by omega)] at values
  omega

private theorem includesFinPhase (s : Snapshot) (f : Values)
    (phase : TypedMachine.eval s f e955 = true ∨ TypedMachine.eval s f e962 = true ∨
      TypedMachine.eval s f e964 = true) : TypedMachine.eval s zeroValues e1674 = true := by
  change TypedMachine.eval s zeroValues e955 = true ∨
    TypedMachine.eval s zeroValues e962 = true ∨ TypedMachine.eval s zeroValues e964 = true at phase
  change (((TypedMachine.eval s zeroValues e1671 || TypedMachine.eval s zeroValues e955) ||
      TypedMachine.eval s zeroValues e962) || TypedMachine.eval s zeroValues e964) = true
  rcases phase with h | h | h <;> simp only [h, Bool.or_true, Bool.true_or]

private theorem finAck (s : Snapshot) (f : Values) (valid : invariantsHold model s = true)
    (phase : TypedMachine.eval s zeroValues e1674 = true)
    (ackNext : TypedMachine.eval s f e764 = true)
    (ackBase : TypedMachine.eval s f e977 = true) : False := by
  have inv : TypedMachine.eval s zeroValues e1679 = true :=
    List.all_eq_true.mp valid e1679 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e1674 || TypedMachine.eval s zeroValues e1678) = true at inv
  simp only [phase, Bool.not_true, Bool.false_or] at inv
  change (TypedMachine.eval s zeroValues e1676 && TypedMachine.eval s zeroValues e1677) = true at inv
  simp only [Bool.and_eq_true] at inv
  have next : TypedMachine.eval s f e763 =
      ValueOps.seqAdd (TypedMachine.eval s f e518) 1 := of_decide_eq_true inv.1
  have base : TypedMachine.eval s f e976 = TypedMachine.eval s f e518 :=
    of_decide_eq_true inv.2
  have a : TypedMachine.eval s f e762 = TypedMachine.eval s f e763 := of_decide_eq_true ackNext
  have b : TypedMachine.eval s f e762 = TypedMachine.eval s f e976 := of_decide_eq_true ackBase
  exact seq_add_one_ne _ (next.symm.trans (a.symm.trans (b.trans base)))

private theorem retransmitLengthNonnegative (s : Snapshot) (f : Values) :
    0 ≤ TypedMachine.eval s f e929 :=
  Int.natCast_nonneg _

private theorem retransmitLengthBound (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) : TypedMachine.eval s f e929 ≤ 16 := by
  have checked : TypedMachine.eval s zeroValues e1691 = true :=
    List.all_eq_true.mp valid e1691 (by rw [model_invariants]; simp)
  have bound : TypedMachine.eval s f e925 + TypedMachine.eval s f e929 ≤ 16 :=
    of_decide_eq_true checked
  have nonnegative : 0 ≤ TypedMachine.eval s f e925 := Int.natCast_nonneg _
  exact Int.le_trans (Int.le_add_of_nonneg_left nonnegative) bound

private theorem oldDistanceCannotFit (base ack : ValueOps.Seq32) (length : Int)
    (ordered : 0 < ValueOps.seqDistance ack base ∧ ValueOps.seqDistance ack base < 2147483648)
    (small : ValueOps.seqDistance base ack ≤ length) (buffer : length ≤ 16) : False := by
  unfold ValueOps.seqDistance at ordered small
  have baseBound := base.isLt
  have ackBound := ack.isLt
  omega

private theorem oldAck (s : Snapshot) (f : Values) (valid : invariantsHold model s = true)
    (within : TypedMachine.eval s f e1262 = true)
    (old : TypedMachine.eval s f e1311 = true) : False := by
  exact oldDistanceCannotFit (TypedMachine.eval s f e976) (TypedMachine.eval s f e762)
    (TypedMachine.eval s f e929) (of_decide_eq_true old) (of_decide_eq_true within)
    (retransmitLengthBound s f valid)

private theorem futureDistanceCannotFit (base ack : ValueOps.Seq32) (length : Int)
    (same : ack = base) (ahead : length + 1 ≤ ValueOps.seqDistance base ack)
    (buffer : 0 ≤ length) : False := by
  rw [same, ValueOps.seqDistance, Int.sub_self, Int.zero_emod] at ahead
  omega

private theorem futureAck (s : Snapshot) (f : Values)
    (duplicate : TypedMachine.eval s f e977 = true)
    (future : TypedMachine.eval s f e1317 = true) : False := by
  exact futureDistanceCannotFit (TypedMachine.eval s f e976) (TypedMachine.eval s f e762)
    (TypedMachine.eval s f e929) (of_decide_eq_true duplicate) (of_decide_eq_true future)
    (retransmitLengthNonnegative s f)

theorem pair_248_249 : PairDisjoint model (rule_248, rule_249) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact complement s f e1278 (leaf s f "LRRR" rule_248 e1278 rfl ha) (leaf s f "LRRR" rule_249 e1284 rfl hb)

theorem pair_250_251 : PairDisjoint model (rule_250, rule_251) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact complement s f e1278 (leaf s f "LRRR" rule_250 e1278 rfl ha) (leaf s f "LRRR" rule_251 e1284 rfl hb)

theorem pair_252_253 : PairDisjoint model (rule_252, rule_253) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact complement s f e1278 (leaf s f "LRRR" rule_252 e1278 rfl ha) (leaf s f "LRRR" rule_253 e1284 rfl hb)

theorem pair_270_273 : PairDisjoint model (rule_270, rule_273) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact complement s f e1400 (leaf s f "LLRRR" rule_270 e1400 rfl ha) (leaf s f "LLRRR" rule_273 e1414 rfl hb)

theorem pair_271_274 : PairDisjoint model (rule_271, rule_274) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact complement s f e1400 (leaf s f "LLRRR" rule_271 e1400 rfl ha) (leaf s f "LLRRR" rule_274 e1414 rfl hb)

theorem pair_272_275 : PairDisjoint model (rule_272, rule_275) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact complement s f e1400 (leaf s f "LLRRR" rule_272 e1400 rfl ha) (leaf s f "LLRRR" rule_275 e1414 rfl hb)

theorem pair_267_273 : PairDisjoint model (rule_267, rule_273) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact conjunctComplement s f e1375 e1391 (leaf s f "LLRRRLR" rule_267 e1375 rfl ha) (leaf s f "LLRRRR" rule_267 e1391 rfl ha)
    (leaf s f "LLRRLR" rule_273 e1412 rfl hb)

theorem pair_268_274 : PairDisjoint model (rule_268, rule_274) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact conjunctComplement s f e1375 e1391 (leaf s f "LLRRRLR" rule_268 e1375 rfl ha) (leaf s f "LLRRRR" rule_268 e1391 rfl ha)
    (leaf s f "LLRRLR" rule_274 e1412 rfl hb)

theorem pair_269_275 : PairDisjoint model (rule_269, rule_275) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact conjunctComplement s f e1375 e1391 (leaf s f "LLRRRLR" rule_269 e1375 rfl ha) (leaf s f "LLRRRR" rule_269 e1391 rfl ha)
    (leaf s f "LLRRLR" rule_275 e1412 rfl hb)

theorem pair_120_121 : PairDisjoint model (rule_120, rule_121) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact finAck s f valid (includesFinPhase s f (Or.inl (leaf s f "LL" rule_120 e955 rfl ha)))
    (leaf s f "LRRL" rule_120 e764 rfl ha) (leaf s f "LRRR" rule_121 e977 rfl hb)

theorem pair_122_123 : PairDisjoint model (rule_122, rule_123) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact finAck s f valid (includesFinPhase s f (Or.inr (Or.inl (leaf s f "LL" rule_122 e962 rfl ha))))
    (leaf s f "LRRL" rule_122 e764 rfl ha) (leaf s f "LRRR" rule_123 e977 rfl hb)

theorem pair_124_125 : PairDisjoint model (rule_124, rule_125) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact finAck s f valid (includesFinPhase s f (Or.inr (Or.inr (leaf s f "LL" rule_124 e964 rfl ha))))
    (leaf s f "LRRL" rule_124 e764 rfl ha) (leaf s f "LRRR" rule_125 e977 rfl hb)

theorem pair_132_135 : PairDisjoint model (rule_132, rule_135) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact finAck s f valid (includesFinPhase s f (Or.inl (leaf s f "LLL" rule_132 e955 rfl ha)))
    (leaf s f "LLRRL" rule_132 e764 rfl ha) (leaf s f "LLRRR" rule_135 e977 rfl hb)

theorem pair_133_136 : PairDisjoint model (rule_133, rule_136) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact finAck s f valid (includesFinPhase s f (Or.inl (leaf s f "LLL" rule_133 e955 rfl ha)))
    (leaf s f "LLRRL" rule_133 e764 rfl ha) (leaf s f "LLRRR" rule_136 e977 rfl hb)

theorem pair_134_137 : PairDisjoint model (rule_134, rule_137) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact finAck s f valid (includesFinPhase s f (Or.inl (leaf s f "LLL" rule_134 e955 rfl ha)))
    (leaf s f "LLRRL" rule_134 e764 rfl ha) (leaf s f "LLRRR" rule_137 e977 rfl hb)

theorem pair_248_254 : PairDisjoint model (rule_248, rule_254) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact oldAck s f valid (leaf s f "LRRLLLRR" rule_248 e1262 rfl ha) (leaf s f "LRRR" rule_254 e1311 rfl hb)

theorem pair_249_254 : PairDisjoint model (rule_249, rule_254) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact oldAck s f valid (leaf s f "LRRLLLRR" rule_249 e1262 rfl ha) (leaf s f "LRRR" rule_254 e1311 rfl hb)

theorem pair_250_254 : PairDisjoint model (rule_250, rule_254) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact oldAck s f valid (leaf s f "LRRLLLRR" rule_250 e1262 rfl ha) (leaf s f "LRRR" rule_254 e1311 rfl hb)

theorem pair_251_254 : PairDisjoint model (rule_251, rule_254) := by
  intro s f valid _
  apply impossible
  intro ha hb
  exact oldAck s f valid (leaf s f "LRRLLLRR" rule_251 e1262 rfl ha) (leaf s f "LRRR" rule_254 e1311 rfl hb)

theorem pair_252_255 : PairDisjoint model (rule_252, rule_255) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact futureAck s f (leaf s f "LRRLLR" rule_252 e977 rfl ha) (leaf s f "LLRRRL" rule_255 e1317 rfl hb)

theorem pair_252_256 : PairDisjoint model (rule_252, rule_256) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact futureAck s f (leaf s f "LRRLLR" rule_252 e977 rfl ha) (leaf s f "LLRRRL" rule_256 e1317 rfl hb)

theorem pair_252_257 : PairDisjoint model (rule_252, rule_257) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact futureAck s f (leaf s f "LRRLLR" rule_252 e977 rfl ha) (leaf s f "LLRRRL" rule_257 e1317 rfl hb)

theorem pair_253_255 : PairDisjoint model (rule_253, rule_255) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact futureAck s f (leaf s f "LRRLLR" rule_253 e977 rfl ha) (leaf s f "LLRRRL" rule_255 e1317 rfl hb)

theorem pair_253_256 : PairDisjoint model (rule_253, rule_256) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact futureAck s f (leaf s f "LRRLLR" rule_253 e977 rfl ha) (leaf s f "LLRRRL" rule_256 e1317 rfl hb)

theorem pair_253_257 : PairDisjoint model (rule_253, rule_257) := by
  intro s f _ _
  apply impossible
  intro ha hb
  exact futureAck s f (leaf s f "LRRLLR" rule_253 e977 rfl ha) (leaf s f "LLRRRL" rule_257 e1317 rfl hb)

private theorem frameMember (position : Nat) (rule : Rule)
    (atPosition : conflictGroup_4[position]? = some rule) : rule ∈ conflictGroup_4 :=
  List.mem_iff_getElem?.mpr ⟨position, atPosition⟩

def control : List (Rule × Rule) :=
  [(rule_120, rule_121),
   (rule_122, rule_123),
   (rule_124, rule_125),
   (rule_132, rule_135),
   (rule_133, rule_136),
   (rule_134, rule_137)]

theorem controlDisjoint : Each (PairDisjoint model) control :=
  ⟨pair_120_121,
   pair_122_123,
   pair_124_125,
   pair_132_135,
   pair_133_136,
   pair_134_137, trivial⟩

theorem controlMembers : Each (fun p => p.1 ∈ conflictGroup_4 ∧ p.2 ∈ conflictGroup_4) control :=
  ⟨⟨frameMember 83 rule_120 rfl, frameMember 84 rule_121 rfl⟩,
   ⟨frameMember 85 rule_122 rfl, frameMember 86 rule_123 rfl⟩,
   ⟨frameMember 87 rule_124 rfl, frameMember 88 rule_125 rfl⟩,
   ⟨frameMember 95 rule_132 rfl, frameMember 98 rule_135 rfl⟩,
   ⟨frameMember 96 rule_133 rfl, frameMember 99 rule_136 rfl⟩,
   ⟨frameMember 97 rule_134 rfl, frameMember 100 rule_137 rfl⟩, trivial⟩

def data : List (Rule × Rule) :=
  [(rule_248, rule_249),
   (rule_248, rule_254),
   (rule_249, rule_254),
   (rule_250, rule_251),
   (rule_250, rule_254),
   (rule_251, rule_254),
   (rule_252, rule_253),
   (rule_252, rule_255),
   (rule_252, rule_256),
   (rule_252, rule_257),
   (rule_253, rule_255),
   (rule_253, rule_256),
   (rule_253, rule_257),
   (rule_267, rule_273),
   (rule_268, rule_274),
   (rule_269, rule_275),
   (rule_270, rule_273),
   (rule_271, rule_274),
   (rule_272, rule_275)]

theorem dataDisjoint : Each (PairDisjoint model) data :=
  ⟨pair_248_249,
   pair_248_254,
   pair_249_254,
   pair_250_251,
   pair_250_254,
   pair_251_254,
   pair_252_253,
   pair_252_255,
   pair_252_256,
   pair_252_257,
   pair_253_255,
   pair_253_256,
   pair_253_257,
   pair_267_273,
   pair_268_274,
   pair_269_275,
   pair_270_273,
   pair_271_274,
   pair_272_275, trivial⟩

theorem dataMembers : Each (fun p => p.1 ∈ conflictGroup_4 ∧ p.2 ∈ conflictGroup_4) data :=
  ⟨⟨frameMember 158 rule_248 rfl, frameMember 159 rule_249 rfl⟩,
   ⟨frameMember 158 rule_248 rfl, frameMember 164 rule_254 rfl⟩,
   ⟨frameMember 159 rule_249 rfl, frameMember 164 rule_254 rfl⟩,
   ⟨frameMember 160 rule_250 rfl, frameMember 161 rule_251 rfl⟩,
   ⟨frameMember 160 rule_250 rfl, frameMember 164 rule_254 rfl⟩,
   ⟨frameMember 161 rule_251 rfl, frameMember 164 rule_254 rfl⟩,
   ⟨frameMember 162 rule_252 rfl, frameMember 163 rule_253 rfl⟩,
   ⟨frameMember 162 rule_252 rfl, frameMember 165 rule_255 rfl⟩,
   ⟨frameMember 162 rule_252 rfl, frameMember 166 rule_256 rfl⟩,
   ⟨frameMember 162 rule_252 rfl, frameMember 167 rule_257 rfl⟩,
   ⟨frameMember 163 rule_253 rfl, frameMember 165 rule_255 rfl⟩,
   ⟨frameMember 163 rule_253 rfl, frameMember 166 rule_256 rfl⟩,
   ⟨frameMember 163 rule_253 rfl, frameMember 167 rule_257 rfl⟩,
   ⟨frameMember 174 rule_267 rfl, frameMember 180 rule_273 rfl⟩,
   ⟨frameMember 175 rule_268 rfl, frameMember 181 rule_274 rfl⟩,
   ⟨frameMember 176 rule_269 rfl, frameMember 182 rule_275 rfl⟩,
   ⟨frameMember 177 rule_270 rfl, frameMember 180 rule_273 rfl⟩,
   ⟨frameMember 178 rule_271 rfl, frameMember 181 rule_274 rfl⟩,
   ⟨frameMember 179 rule_272 rfl, frameMember 182 rule_275 rfl⟩, trivial⟩

end TCPIPFramePairs

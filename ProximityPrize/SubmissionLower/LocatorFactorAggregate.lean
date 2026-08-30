import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.D


namespace ProximityPrize.SubmissionLower.LocatorFactorAggregate
open scoped BigOperators
open RCN095

set_option maxRecDepth 2048
set_option maxHeartbeats 300000

def middle (p:FlagDegree):ℕ:=p.yz+p.all
def total (p:FlagDegree):ℕ:=p.zOnly+p.yz+p.all
def Below (p q:FlagDegree):Prop:=
  p.all≤q.all ∧ middle p≤middle q ∧ total p≤total q

def cap (t y s:ℕ):FlagDegree:=⟨t - y,y - s,s⟩

theorem cap_cumulative (t y s:ℕ) (hsy:s≤y) (hyt:y≤t):
    (cap t y s).all=s ∧ middle (cap t y s)=y ∧ total (cap t y s)=t:=by
  dsimp [cap,middle,total]
  omega


theorem mixed_expansion (p q r:FlagDegree):
    flagMixed p q r=
      (q.all*r.all+q.yz*r.all+q.all*r.yz)*total p+
      (q.zOnly*r.all+q.all*r.zOnly)*middle p+
      (q.yz*r.yz+q.zOnly*r.yz+q.yz*r.zOnly)*p.all:=by
  simp only [flagMixed,middle,total]
  ring

theorem mixed_mono_first {p P:FlagDegree} (h:Below p P) (q r:FlagDegree):
    flagMixed p q r≤flagMixed P q r:=by
  rw [mixed_expansion p q r,mixed_expansion P q r]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.2) (Nat.mul_le_mul_left _ h.2.1))
    (Nat.mul_le_mul_left _ h.1)

theorem mixed_mono_second (p:FlagDegree) {q Q:FlagDegree}
    (h:Below q Q) (r:FlagDegree):flagMixed p q r≤flagMixed p Q r:=by
  calc
    flagMixed p q r=flagMixed q p r:=by unfold flagMixed; ring
    _≤flagMixed Q p r:=mixed_mono_first h p r
    _=flagMixed p Q r:=by unfold flagMixed; ring

theorem mixed_mono_third (p q:FlagDegree) {r R:FlagDegree}
    (h:Below r R):flagMixed p q r≤flagMixed p q R:=by
  calc
    flagMixed p q r=flagMixed r q p:=by unfold flagMixed; ring
    _≤flagMixed R q p:=mixed_mono_first h q p
    _=flagMixed p q R:=by unfold flagMixed; ring

theorem mixed_mono_tails (p:FlagDegree) {q Q r R:FlagDegree}
    (hq:Below q Q) (hr:Below r R):flagMixed p q r≤flagMixed p Q R:=
  (mixed_mono_second p hq r).trans (mixed_mono_third p Q hr)

theorem sum_mixed_le {I:Type*} [Fintype I]
    (p:I → FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i,(p i).all)≤P.all)
    (hy:(∑ i,middle (p i))≤middle P)
    (ht:(∑ i,total (p i))≤total P):
    (∑ i,flagMixed (p i) q r)≤flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _=>mixed_expansion (p i) q r),
    mixed_expansion P q r]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)

def padS (p:FlagDegree):ℕ:=max p.all 2
def padY (p:FlagDegree):ℕ:=max (middle p) (padS p+1)
def padT (p:FlagDegree):ℕ:=max (total p) (padY p)

def paddedTail (p:FlagDegree) (d:ℕ):FlagDegree:=
  ⟨2*(padT p - padY p)*d,
    1+2*(padY p - padS p)*d,
    2*(padS p - 1)*d⟩


def paddedCost (d e:ℕ) (p:FlagDegree):ℕ:=
  flagMixed p (paddedTail p d) (paddedTail p e)

theorem paddedTail_cumulative (p:FlagDegree) (d:ℕ):
    (paddedTail p d).all=2*(padS p - 1)*d ∧
    middle (paddedTail p d)=1+2*(padY p - 1)*d ∧
    total (paddedTail p d)=1+2*(padT p - 1)*d:=by
  have hs:1≤padS p:=by
    have h:2≤padS p:=le_max_right _ _
    omega
  have hy:padS p+1≤padY p:=le_max_right _ _
  have ht:padY p≤padT p:=le_max_right _ _
  have hyadd:padY p - padS p+(padS p - 1)=padY p - 1:=by omega
  have htadd:padT p - padY p+(padY p - padS p)+(padS p - 1)=
      padT p - 1:=by omega
  refine ⟨rfl,?_,?_⟩
  · change (1+2*(padY p - padS p)*d)+2*(padS p - 1)*d=_
    calc
      _=1+2*(padY p - padS p+(padS p - 1))*d:=by ring
      _=_:=by rw [hyadd]
  · change (2*(padT p - padY p)*d+
      (1+2*(padY p - padS p)*d))+2*(padS p - 1)*d=_
    calc
      _=1+2*(padT p - padY p+(padY p - padS p)+
        (padS p - 1))*d:=by ring
      _=_:=by rw [htadd]

theorem padding_mono {p q:FlagDegree} (h:Below p q):
    padS p≤padS q ∧ padY p≤padY q ∧ padT p≤padT q:=by
  have hs:padS p≤padS q:=max_le_max h.1 (Nat.le_refl 2)
  have hy:padY p≤padY q:=max_le_max h.2.1 (Nat.add_le_add_right hs 1)
  have ht:padT p≤padT q:=max_le_max h.2.2 hy
  exact ⟨hs,hy,ht⟩

theorem paddedTail_mono (d:ℕ) {p q:FlagDegree} (h:Below p q):
    Below (paddedTail p d) (paddedTail q d):=by
  have hp:=paddedTail_cumulative p d
  have hq:=paddedTail_cumulative q d
  have hc:=padding_mono h
  have hm {a b:ℕ} (hab:a≤b):2*(a - 1)*d≤2*(b - 1)*d:=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hab 1))
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2]
  exact ⟨hm hc.1,Nat.add_le_add_left (hm hc.2.1) 1,
    Nat.add_le_add_left (hm hc.2.2) 1⟩

theorem paddedCost_mono (d e:ℕ) {p q:FlagDegree} (h:Below p q):
    paddedCost d e p≤paddedCost d e q:=by
  exact (mixed_mono_first h _ _).trans
    (mixed_mono_tails q (paddedTail_mono d h) (paddedTail_mono e h))


theorem merge_padded_costs {I:Type*} [Fintype I]
    (d e:ℕ) (p:I → FlagDegree) (P:FlagDegree)
    (hs:(∑ i,(p i).all)≤P.all)
    (hy:(∑ i,middle (p i))≤middle P)
    (ht:(∑ i,total (p i))≤total P):
    (∑ i,paddedCost d e (p i))≤paddedCost d e P:=by
  classical
  letI:DecidableEq I:=Classical.decEq I
  have hi (i:I):Below (p i) P:=by
    exact ⟨(Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans hs,
      (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans hy,
      (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans ht⟩
  calc
    (∑ i,paddedCost d e (p i))≤
        ∑ i,flagMixed (p i) (paddedTail P d) (paddedTail P e):=
      Finset.sum_le_sum (fun i _=>
        mixed_mono_tails (p i) (paddedTail_mono d (hi i)) (paddedTail_mono e (hi i)))
    _≤paddedCost d e P:=sum_mixed_le p P _ _ hs hy ht

theorem paddedTail_cap (t y s d:ℕ)
    (hs:2≤s) (hy:s+1≤y) (ht:y≤t):
    paddedTail (cap t y s) d=
      ⟨2*(t - y)*d,1+2*(y - s)*d,2*(s - 1)*d⟩:=by
  have hc:=cap_cumulative t y s (by omega) ht
  have hps:padS (cap t y s)=s:=by
    change max s 2=s
    exact max_eq_left hs
  have hpy:padY (cap t y s)=y:=by
    unfold padY
    rw [hc.2.1,hps,max_eq_left hy]
  have hpt:padT (cap t y s)=t:=by
    unfold padT
    rw [hc.2.2,hpy,max_eq_left ht]
  simp only [paddedTail,hps,hpy,hpt]


theorem middle_le_total (p:FlagDegree):middle p≤total p:=by
  dsimp [middle,total]
  omega

theorem all_le_total (p:FlagDegree):p.all≤total p:=by
  dsimp [total]
  omega

theorem below_cap_of_bounds (p:FlagDegree) (t y s:ℕ)
    (hsy:s≤y) (hyt:y≤t)
    (hs:p.all≤s) (hy:middle p≤y) (ht:total p≤t):
    Below p (cap t y s):=by
  have hc:=cap_cumulative t y s hsy hyt
  unfold Below
  rw [hc.1,hc.2.1,hc.2.2]
  exact ⟨hs,hy,ht⟩

private theorem below_total_flag (p:FlagDegree):
    Below p ⟨0,0,total p⟩:=by
  unfold Below
  refine ⟨all_le_total p,?_,?_⟩
  · simpa only [middle,Nat.zero_add] using middle_le_total p
  · simp only [total,Nat.zero_add,le_refl]

private def diagonalRate (u s:ℕ):ℕ:=
  flagMixed ⟨0,0,1⟩
    (paddedTail (cap u u s) 131072)
    (paddedTail (cap u u s) 131073)

private theorem cost_le_diagonal_rate (p:FlagDegree) (u s:ℕ)
    (h:Below p (cap u u s)):
    paddedCost 131072 131073 p≤diagonalRate u s*total p:=by
  calc
    _≤flagMixed p (paddedTail (cap u u s) 131072)
        (paddedTail (cap u u s) 131073):=
      mixed_mono_tails p (paddedTail_mono 131072 h) (paddedTail_mono 131073 h)
    _≤flagMixed ⟨0,0,total p⟩ (paddedTail (cap u u s) 131072)
        (paddedTail (cap u u s) 131073):=
      mixed_mono_first (below_total_flag p) _ _
    _=diagonalRate u s*total p:=by
      simp only [diagonalRate,flagMixed]
      ring

private theorem affine59 (t:ℕ) (ht:59≤t):
    paddedCost 131072 131073 (cap t 59 9)+5930261250834585=
      186093771685922*t:=by
  have hsub:t - 59+59=t:=Nat.sub_add_cancel ht
  unfold paddedCost
  rw [paddedTail_cap t 59 9 131072 (by decide) (by decide) ht,
    paddedTail_cap t 59 9 131073 (by decide) (by decide) ht]
  simp only [cap,flagMixed]
  ring_nf
  omega

private theorem middle_tail_formula59 (p:FlagDegree):
    flagMixed p (paddedTail (cap 59 59 9) 131072)
        (paddedTail (cap 59 59 9) 131073)=
      59374085079056*total p+171800028774501*p.all:=by
  norm_num [paddedTail,padT,padY,padS,cap,total,middle,flagMixed]
  ring

private theorem middle_cost_le (p:FlagDegree) (u s a b:ℕ)
    (h:Below p (cap u u s))
    (heq:flagMixed p (paddedTail (cap u u s) 131072)
      (paddedTail (cap u u s) 131073)=a*total p+b*p.all):
    paddedCost 131072 131073 p≤a*total p+b*s:=by
  calc
    _≤flagMixed p (paddedTail (cap u u s) 131072)
        (paddedTail (cap u u s) 131073):=
      mixed_mono_tails p (paddedTail_mono 131072 h) (paddedTail_mono 131073 h)
    _=a*total p+b*p.all:=heq
    _≤a*total p+b*s:=
      Nat.add_le_add_left (Nat.mul_le_mul_left b h.1) _

private abbrev bound6742:ℕ:=272527456851746043

private theorem low_scale {c t:ℕ} (hc:c≤186093771685922*t):
    1445*c≤bound6742*t:=by
  calc
    1445*c≤1445*(186093771685922*t):=Nat.mul_le_mul_left 1445 hc
    _=(1445*186093771685922)*t:=by ring
    _≤bound6742*t:=Nat.mul_le_mul_right t (by decide)

private theorem low_rate (p:FlagDegree) (hs:p.all≤9)
    (hy:middle p≤59) (ht:total p≤1445):
    1445*paddedCost 131072 131073 p≤bound6742*total p:=by
  have hn:=middle_le_total p
  by_cases ht12:total p≤12
  · have hb:=below_cap_of_bounds p 12 12 10 (by decide) (by decide)
      (by omega) (hn.trans ht12) ht12
    have hc:=cost_le_diagonal_rate p 12 10 hb
    exact low_scale (hc.trans (by
      unfold diagonalRate
      norm_num [paddedTail,padT,padY,padS,cap,total,middle,flagMixed]
      omega))
  · by_cases ht59:total p≤59
    · have hb:=below_cap_of_bounds p 59 59 9 (by decide) (by decide) hs hy ht59
      have hc:=middle_cost_le p 59 9 59374085079056 171800028774501
        hb (middle_tail_formula59 p)
      apply low_scale
      exact hc.trans (by omega)
    · have hlo:59≤total p:=by omega
      have hb:=below_cap_of_bounds p (total p) 59 9 (by decide) hlo hs hy (le_refl _)
      apply low_scale
      calc
        paddedCost 131072 131073 p≤
            paddedCost 131072 131073 (cap (total p) 59 9):=
          paddedCost_mono 131072 131073 hb
        _≤186093771685922*total p:=by
          have h:=affine59 (total p) hlo
          omega

private theorem sum_mixed_le_on {I:Type*} [Fintype I] (S:Finset I)
    (p:I → FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i∈S,(p i).all)≤P.all)
    (hy:(∑ i∈S,middle (p i))≤middle P)
    (ht:(∑ i∈S,total (p i))≤total P):
    (∑ i∈S,flagMixed (p i) q r)≤flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _=>mixed_expansion (p i) q r),mixed_expansion P q r]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)

private theorem merge_on {I:Type*} [Fintype I] (S:Finset I)
    (p:I → FlagDegree) (P:FlagDegree)
    (hs:(∑ i∈S,(p i).all)≤P.all)
    (hy:(∑ i∈S,middle (p i))≤middle P)
    (ht:(∑ i∈S,total (p i))≤total P):
    (∑ i∈S,paddedCost 131072 131073 (p i))≤paddedCost 131072 131073 P:=by
  have hi (i:I) (hiS:i∈S):Below (p i) P:=by
    exact ⟨(Finset.single_le_sum (fun _ _=>Nat.zero_le _) hiS).trans hs,
      (Finset.single_le_sum (fun _ _=>Nat.zero_le _) hiS).trans hy,
      (Finset.single_le_sum (fun _ _=>Nat.zero_le _) hiS).trans ht⟩
  calc
    _≤∑ i∈S,flagMixed (p i) (paddedTail P 131072) (paddedTail P 131073):=
      Finset.sum_le_sum (fun i hiS=>mixed_mono_tails (p i)
        (paddedTail_mono 131072 (hi i hiS)) (paddedTail_mono 131073 (hi i hiS)))
    _≤paddedCost 131072 131073 P:=sum_mixed_le_on S p P _ _ hs hy ht

private theorem pair10 (a b:ℕ) (ha:a≤1386) (hab:a+b≤1404)
    (hb0:1≤b) (hb:b≤45):
    paddedCost 131072 131073 (cap (10+b+a) (10+b) 10)+
      paddedCost 131072 131073 (cap (1435-b-a) (49-b) 3)≤bound6742:=by
  have h1:2≤10:=by omega
  have h2:10+1≤10+b:=by omega
  have h3:10+b≤10+b+a:=by omega
  have h4:2≤3:=by omega
  have h5:3+1≤49-b:=by omega
  have h6:49-b≤1435-b-a:=by omega
  simp only [paddedCost]
  rw [paddedTail_cap _ _ _ 131072 h1 h2 h3,paddedTail_cap _ _ _ 131073 h1 h2 h3,
    paddedTail_cap _ _ _ 131072 h4 h5 h6,paddedTail_cap _ _ _ 131073 h4 h5 h6]
  simp only [cap]
  have e1:10+b+a-(10+b)=a:=by omega
  have e2:10+b-10=b:=by omega
  have e3:10-1=9:=by omega
  have e4:1435-b-a-(49-b)=1386-a:=by omega
  have e5:49-b-3=46-b:=by omega
  have e6:3-1=2:=by omega
  rw [e1,e2,e3,e4,e5,e6]
  simp only [flagMixed]
  ring_nf
  have ea:1386-a+a=1386:=Nat.sub_add_cancel ha
  have eb:46-b+b=46:=Nat.sub_add_cancel (by omega:b≤46)
  nlinarith

private theorem pair11 (a b:ℕ) (ha:a≤1386) (hab:a+b≤1403)
    (hb0:1≤b) (hb:b≤41):
    paddedCost 131072 131073 (cap (11+b+a) (11+b) 11)+
      paddedCost 131072 131073 (cap (1434-b-a) (48-b) 2)≤bound6742:=by
  have h1:2≤11:=by omega
  have h2:11+1≤11+b:=by omega
  have h3:11+b≤11+b+a:=by omega
  have h4:2≤2:=by omega
  have h5:2+1≤48-b:=by omega
  have h6:48-b≤1434-b-a:=by omega
  simp only [paddedCost]
  rw [paddedTail_cap _ _ _ 131072 h1 h2 h3,paddedTail_cap _ _ _ 131073 h1 h2 h3,
    paddedTail_cap _ _ _ 131072 h4 h5 h6,paddedTail_cap _ _ _ 131073 h4 h5 h6]
  simp only [cap]
  have e1:11+b+a-(11+b)=a:=by omega
  have e2:11+b-11=b:=by omega
  have e3:11-1=10:=by omega
  have e4:1434-b-a-(48-b)=1386-a:=by omega
  have e5:48-b-2=46-b:=by omega
  have e6:2-1=1:=by omega
  rw [e1,e2,e3,e4,e5,e6]
  simp only [flagMixed]
  ring_nf
  have ea:1386-a+a=1386:=Nat.sub_add_cancel ha
  have eb:46-b+b=46:=Nat.sub_add_cancel (by omega:b≤46)
  nlinarith

private theorem pair12 (a b:ℕ) (ha:a≤1386) (hab:a+b≤1402)
    (hb0:1≤b) (hb:b≤36):
    paddedCost 131072 131073 (cap (12+b+a) (12+b) 12)+
      paddedCost 131072 131073 (cap (1433-b-a) (47-b) 2)≤bound6742:=by
  have h1:2≤12:=by omega
  have h2:12+1≤12+b:=by omega
  have h3:12+b≤12+b+a:=by omega
  have h4:2≤2:=by omega
  have h5:2+1≤47-b:=by omega
  have h6:47-b≤1433-b-a:=by omega
  simp only [paddedCost]
  rw [paddedTail_cap _ _ _ 131072 h1 h2 h3,paddedTail_cap _ _ _ 131073 h1 h2 h3,
    paddedTail_cap _ _ _ 131072 h4 h5 h6,paddedTail_cap _ _ _ 131073 h4 h5 h6]
  simp only [cap]
  have e1:12+b+a-(12+b)=a:=by omega
  have e2:12+b-12=b:=by omega
  have e3:12-1=11:=by omega
  have e4:1433-b-a-(47-b)=1386-a:=by omega
  have e5:47-b-2=45-b:=by omega
  have e6:2-1=1:=by omega
  rw [e1,e2,e3,e4,e5,e6]
  simp only [flagMixed]
  ring_nf
  have ea:1386-a+a=1386:=Nat.sub_add_cancel ha
  have eb:45-b+b=45:=Nat.sub_add_cancel (by omega:b≤45)
  nlinarith

private theorem self_cap (p:FlagDegree):p=cap (total p) (middle p) p.all:=by
  cases p
  simp only [cap,total,middle]
  congr<;>omega

theorem aggregate_6742 {I:Type*} [Fintype I] (p:I → FlagDegree)
    (hpos:∀ i,0<(p i).all)
    (hsum:(∑ i,(p i).all)≤13)
    (hysum:(∑ i,middle (p i))≤59)
    (htsum:(∑ i,total (p i))≤1445)
    (h10:∀ i,(p i).all=10 → middle (p i)≤56)
    (h11:∀ i,(p i).all=11 → middle (p i)≤52)
    (h12:∀ i,(p i).all=12 → middle (p i)≤48)
    (h13:∀ i,(p i).all=13 → middle (p i)≤44)
    (ht10:∀ i,(p i).all=10 → total (p i)≤1414)
    (ht11:∀ i,(p i).all=11 → total (p i)≤1414)
    (ht12:∀ i,(p i).all=12 → total (p i)≤1414)
    (ht13:∀ i,(p i).all=13 → total (p i)≤1413):
    (∑ i,paddedCost 131072 131073 (p i))≤bound6742:=by
  classical
  letI:DecidableEq I:=Classical.decEq I
  by_cases hhigh:∃ i,10≤(p i).all
  · obtain ⟨i0,hi0⟩:=hhigh
    let S:Finset I:=Finset.univ.erase i0
    let R:=(p i0).all
    let y:=middle (p i0)
    let t:=total (p i0)
    have hRi:R=(p i0).all:=rfl
    have hRy:R≤y:=by dsimp [R,y,middle]; omega
    have hyt:y≤t:=middle_le_total (p i0)
    have hR13:R≤13:=
      (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i0)).trans hsum
    have hsE:(∑ i∈S,(p i).all)+R≤13:=by
      rw [show (∑ i∈S,(p i).all)+R=∑ i,(p i).all by
        simpa only [S,R] using Finset.sum_erase_add Finset.univ (fun i=>(p i).all)
          (Finset.mem_univ i0)]
      exact hsum
    have hyE:(∑ i∈S,middle (p i))+y≤59:=by
      rw [show (∑ i∈S,middle (p i))+y=∑ i,middle (p i) by
        simpa only [S,y] using Finset.sum_erase_add Finset.univ (fun i=>middle (p i))
          (Finset.mem_univ i0)]
      exact hysum
    have htE:(∑ i∈S,total (p i))+t≤1445:=by
      rw [show (∑ i∈S,total (p i))+t=∑ i,total (p i) by
        simpa only [S,t] using Finset.sum_erase_add Finset.univ (fun i=>total (p i))
          (Finset.mem_univ i0)]
      exact htsum
    have hyEt:(∑ i∈S,middle (p i))≤∑ i∈S,total (p i):=
      Finset.sum_le_sum (fun i _=>middle_le_total (p i))
    have hcostE:(∑ i,paddedCost 131072 131073 (p i))=
        (∑ i∈S,paddedCost 131072 131073 (p i))+
          paddedCost 131072 131073 (p i0):=by
      symm
      simpa only [S] using Finset.sum_erase_add Finset.univ
        (fun i=>paddedCost 131072 131073 (p i)) (Finset.mem_univ i0)
    have hp:p i0=cap t y R:=by simpa only [t,y,R] using self_cap (p i0)
    have hcases:R=10 ∨ R=11 ∨ R=12 ∨ R=13:=by omega
    rcases hcases with hR | hR | hR | hR
    · have hycap:y≤56:=by simpa only [R] using h10 i0 (by simpa only [R] using hR)
      have htcap:t≤1414:=by simpa only [R] using ht10 i0 (by simpa only [R] using hR)
      let a:=t-y
      let b:=y-R
      have hyeq:y=10+b:=by dsimp [b]; omega
      have hteq:t=10+b+a:=by dsimp [a]; omega
      have hb:b≤46:=by omega
      have hab:a+b≤1404:=by omega
      by_cases ha:a≤1386
      · by_cases hb0:b=0
        · have hmain:paddedCost 131072 131073 (p i0)≤
              paddedCost 131072 131073 (cap 1414 11 10):=by
            apply paddedCost_mono 131072 131073
            apply below_cap_of_bounds (p i0) 1414 11 10 (by decide) (by decide)
            · simpa only [R] using hR.le
            · dsimp [y] at hyeq ⊢; omega
            · simpa only [t] using htcap
          have hrest:=merge_on S p (cap 1445 49 3)
            (by rw [(cap_cumulative 1445 49 3 (by decide) (by decide)).1]; omega)
            (by rw [(cap_cumulative 1445 49 3 (by decide) (by decide)).2.1]; omega)
            (by rw [(cap_cumulative 1445 49 3 (by decide) (by decide)).2.2]; omega)
          rw [hcostE]
          exact (Nat.add_le_add hrest hmain).trans (by decide)
        · by_cases hb46:b=46
          · have hmain:paddedCost 131072 131073 (p i0)≤
                paddedCost 131072 131073 (cap 1414 56 10):=by
              apply paddedCost_mono 131072 131073
              apply below_cap_of_bounds (p i0) 1414 56 10 (by decide) (by decide)
              · simpa only [R] using hR.le
              · dsimp [y] at hyeq ⊢; omega
              · simpa only [t] using htcap
            have hrest:=merge_on S p (cap 1389 3 3)
              (by rw [(cap_cumulative 1389 3 3 (by decide) (by decide)).1]; omega)
              (by rw [(cap_cumulative 1389 3 3 (by decide) (by decide)).2.1]; omega)
              (by rw [(cap_cumulative 1389 3 3 (by decide) (by decide)).2.2]; omega)
            rw [hcostE]
            exact (Nat.add_le_add hrest hmain).trans (by decide)
          · have hrest:=merge_on S p (cap (1435-b-a) (49-b) 3)
              (by rw [(cap_cumulative (1435-b-a) (49-b) 3 (by omega) (by omega)).1]; omega)
              (by rw [(cap_cumulative (1435-b-a) (49-b) 3 (by omega) (by omega)).2.1]; omega)
              (by rw [(cap_cumulative (1435-b-a) (49-b) 3 (by omega) (by omega)).2.2]; omega)
            rw [hcostE,hp,hR,hyeq,hteq]
            exact (Nat.add_le_add hrest le_rfl).trans
              (by simpa [Nat.add_comm] using pair10 a b ha hab (by omega) (by omega))
      · have hy27:y≤27:=by omega
        have hmain:paddedCost 131072 131073 (p i0)≤
            paddedCost 131072 131073 (cap 1414 27 10):=by
          apply paddedCost_mono 131072 131073
          exact below_cap_of_bounds (p i0) 1414 27 10 (by decide) (by decide)
            (by simpa only [R] using hR.le) hy27 htcap
        have hrest:=merge_on S p (cap 48 48 3)
          (by rw [(cap_cumulative 48 48 3 (by decide) (by decide)).1]; omega)
          (by rw [(cap_cumulative 48 48 3 (by decide) (by decide)).2.1]; omega)
          (by rw [(cap_cumulative 48 48 3 (by decide) (by decide)).2.2]; omega)
        rw [hcostE]
        exact (Nat.add_le_add hrest hmain).trans (by decide)
    · have hycap:y≤52:=by simpa only [R] using h11 i0 (by simpa only [R] using hR)
      have htcap:t≤1414:=by simpa only [R] using ht11 i0 (by simpa only [R] using hR)
      let a:=t-y
      let b:=y-R
      have hyeq:y=11+b:=by dsimp [b]; omega
      have hteq:t=11+b+a:=by dsimp [a]; omega
      have hb:b≤41:=by omega
      have hab:a+b≤1403:=by omega
      by_cases ha:a≤1386
      · by_cases hb0:b=0
        · have hmain:=paddedCost_mono 131072 131073
              (below_cap_of_bounds (p i0) 1414 12 11 (by decide) (by decide)
                (by simpa only [R] using hR.le) (by omega) htcap)
          have hrest:=merge_on S p (cap 1445 48 2)
            (by rw [(cap_cumulative 1445 48 2 (by decide) (by decide)).1]; omega)
            (by rw [(cap_cumulative 1445 48 2 (by decide) (by decide)).2.1]; omega)
            (by rw [(cap_cumulative 1445 48 2 (by decide) (by decide)).2.2]; omega)
          rw [hcostE]
          exact (Nat.add_le_add hrest hmain).trans (by decide)
        · have hrest:=merge_on S p (cap (1434-b-a) (48-b) 2)
            (by rw [(cap_cumulative (1434-b-a) (48-b) 2 (by omega) (by omega)).1]; omega)
            (by rw [(cap_cumulative (1434-b-a) (48-b) 2 (by omega) (by omega)).2.1]; omega)
            (by rw [(cap_cumulative (1434-b-a) (48-b) 2 (by omega) (by omega)).2.2]; omega)
          rw [hcostE,hp,hR,hyeq,hteq]
          exact (Nat.add_le_add hrest le_rfl).trans
            (by simpa [Nat.add_comm] using pair11 a b ha hab (by omega) hb)
      · have hy27:y≤27:=by omega
        have hmain:=paddedCost_mono 131072 131073
          (below_cap_of_bounds (p i0) 1414 27 11 (by decide) (by decide)
            (by simpa only [R] using hR.le) hy27 htcap)
        have hrest:=merge_on S p (cap 48 48 3)
          (by rw [(cap_cumulative 48 48 3 (by decide) (by decide)).1]; omega)
          (by rw [(cap_cumulative 48 48 3 (by decide) (by decide)).2.1]; omega)
          (by rw [(cap_cumulative 48 48 3 (by decide) (by decide)).2.2]; omega)
        rw [hcostE]
        exact (Nat.add_le_add hrest hmain).trans (by decide)
    · have hycap:y≤48:=by simpa only [R] using h12 i0 (by simpa only [R] using hR)
      have htcap:t≤1414:=by simpa only [R] using ht12 i0 (by simpa only [R] using hR)
      let a:=t-y
      let b:=y-R
      have hyeq:y=12+b:=by dsimp [b]; omega
      have hteq:t=12+b+a:=by dsimp [a]; omega
      have hb:b≤36:=by omega
      have hab:a+b≤1402:=by omega
      by_cases ha:a≤1386
      · by_cases hb0:b=0
        · have hmain:=paddedCost_mono 131072 131073
              (below_cap_of_bounds (p i0) 1414 13 12 (by decide) (by decide)
                (by simpa only [R] using hR.le) (by omega) htcap)
          have hrest:=merge_on S p (cap 1445 47 2)
            (by rw [(cap_cumulative 1445 47 2 (by decide) (by decide)).1]; omega)
            (by rw [(cap_cumulative 1445 47 2 (by decide) (by decide)).2.1]; omega)
            (by rw [(cap_cumulative 1445 47 2 (by decide) (by decide)).2.2]; omega)
          rw [hcostE]
          exact (Nat.add_le_add hrest hmain).trans (by decide)
        · have hrest:=merge_on S p (cap (1433-b-a) (47-b) 2)
            (by rw [(cap_cumulative (1433-b-a) (47-b) 2 (by omega) (by omega)).1]; omega)
            (by rw [(cap_cumulative (1433-b-a) (47-b) 2 (by omega) (by omega)).2.1]; omega)
            (by rw [(cap_cumulative (1433-b-a) (47-b) 2 (by omega) (by omega)).2.2]; omega)
          rw [hcostE,hp,hR,hyeq,hteq]
          exact (Nat.add_le_add hrest le_rfl).trans
            (by simpa [Nat.add_comm] using pair12 a b ha hab (by omega) hb)
      · have hy27:y≤27:=by omega
        have hmain:=paddedCost_mono 131072 131073
          (below_cap_of_bounds (p i0) 1414 27 12 (by decide) (by decide)
            (by simpa only [R] using hR.le) hy27 htcap)
        have hrest:=merge_on S p (cap 48 48 3)
          (by rw [(cap_cumulative 48 48 3 (by decide) (by decide)).1]; omega)
          (by rw [(cap_cumulative 48 48 3 (by decide) (by decide)).2.1]; omega)
          (by rw [(cap_cumulative 48 48 3 (by decide) (by decide)).2.2]; omega)
        rw [hcostE]
        exact (Nat.add_le_add hrest hmain).trans (by decide)
    · have hycap:y≤44:=by simpa only [R] using h13 i0 (by simpa only [R] using hR)
      have htcap:t≤1413:=by simpa only [R] using ht13 i0 (by simpa only [R] using hR)
      have hSempty:S=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have hsJ:=Finset.single_le_sum
          (fun i _=>Nat.zero_le ((p i).all)) hj
        have hpj:=hpos j
        omega
      have hmain:=paddedCost_mono 131072 131073
        (below_cap_of_bounds (p i0) 1413 44 13 (by decide) (by decide)
          (by simpa only [R] using hR.le) hycap htcap)
      rw [hcostE,hSempty]
      simp only [Finset.sum_empty,zero_add]
      exact hmain.trans (by decide)
  · have hsmall (i:I):(p i).all≤9:=by
      by_contra h
      exact hhigh ⟨i,by omega⟩
    have hscaled:1445*(∑ i,paddedCost 131072 131073 (p i))≤
        1445*bound6742:=by
      calc
        _=∑ i,1445*paddedCost 131072 131073 (p i):=by rw [Finset.mul_sum]
        _≤∑ i,bound6742*total (p i):=
          Finset.sum_le_sum (fun i _=>low_rate (p i) (hsmall i)
            ((Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans hysum)
            ((Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans htsum))
        _=bound6742*(∑ i,total (p i)):=by rw [Finset.mul_sum]
        _≤bound6742*1445:=Nat.mul_le_mul_left _ htsum
        _=1445*bound6742:=by ring
    exact Nat.le_of_mul_le_mul_left hscaled (by decide)

end ProximityPrize.SubmissionLower.LocatorFactorAggregate

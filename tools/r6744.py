#!/usr/bin/env python3
from pathlib import Path
import re,subprocess,sys
R=Path('ProximityPrize/SubmissionLower'); F=sorted(R.glob('Locator*.lean'))+[R/'Solution.lean']
if not (R/'score.txt').exists(): raise SystemExit('run at repo root')
def nrep(s,a,b): return re.sub(rf'(?<!\d){a}(?!\d)',b,s)
def req(s,a,b):
 if a not in s: raise SystemExit(f'missing: {a}')
 return s.replace(a,b)
G={'80191':'80201','80192':'80202','181953':'181943','50882':'50872','10264575':'10265855','23289857':'23288577','12736710':'13463782','11463039':'12008238','8187885':'8187435','15829911':'15829041','1470':'1497','237171134622841770':'241613533669933335','274980727060991165':'274980727043561565','1050403922':'1067833522'}
X={'4034312100':'5197898453','2963218530':'3414052680','116336668':'118529824','4953442449347':'6776939096664','2948801310715':'3688325558435','25157355706':'9593123806','58861789':'87725323','116219161506644':'118377111859182','777390425324962':'874095391362982','1010149254715173':'1028905445705819','239074893464388550':'243634911618861319','2939727658':'2940232561','44842':'549745','1525':'1550','53446652327312':'54322826912195','1347234':'1356605','4890686735920':'6706943447457','4853542426374':'6659538848145','4934324508280':'6770681380408','2882963457372':'3682528759190','6576386':'7303458','5921030':'6648102','5527816':'6254888','3729860':'4275059','157377088520227':'157377134395427','5243128521227636':'5243128745360666','161319023345703':'161319074463783','5089003231495260':'5089003506746360','162477776896043':'162477833257003','4837165034277704':'4837165365889754','164529897013295':'164529958617135','4687813986701880':'4687814379917760','156445740171315':'156445807018035','4098487481801004':'4098487941863594','52028314943505':'52028337225745','143166160058792':'143166297684402','53355027431443':'53355052335123','117290853153182':'117290977671592','53754012827669':'53754040352789','93992565946772':'93992677357982','54445060325399':'54445090471959','77209390365068':'77209491290518','51768802344985':'51768835112985','55127050631552':'55127135828362','12038825741428870':'12035132012537930','9615747195338752':'9613857382203392','10356986788911876':'10354066163964636','2622478326693888':'2621962922754048','5244956653387776':'5243925845508096','7905698466823366':'7901489333992556','7601568605841540':'7598304378267720','6461508428997962':'6456697986983092'}
for p in F:
 s=p.read_text().replace('6743','6744')
 for a,b in G.items(): s=nrep(s,a,b)
 s=re.sub(r'13463782(\s+)131071(\s+)100000(\s+)20(\s+)70',r'13463782\g<1>131071\g<2>110000\g<3>21\g<4>74',s)
 s=re.sub(r'12008238(\s+)131071(\s+)100000(\s+)18(\s+)63',r'12008238\g<1>131071\g<2>100000\g<3>19\g<4>66',s)
 s=re.sub(r'13463782(\s+)131071(\s+)100000(\s+)20',r'13463782\g<1>131071\g<2>110000\g<3>21',s)
 s=re.sub(r'12008238(\s+)131071(\s+)100000(\s+)18',r'12008238\g<1>131071\g<2>100000\g<3>19',s)
 s=re.sub(r'localRankBound(\s+)70(\s+)100000(\s+)20',r'localRankBound\g<1>74\g<2>110000\g<3>21',s)
 s=re.sub(r'localRankBound(\s+)63(\s+)100000(\s+)18',r'localRankBound\g<1>66\g<2>100000\g<3>19',s)
 s=re.sub(r'\b70(\s+)\*(\s+)agreements\b',r'74\g<1>*\g<2>agreements',s)
 s=re.sub(r'\b63(\s+)\*(\s+)agreements\b',r'66\g<1>*\g<2>agreements',s)
 for a,b in X.items(): s=nrep(s,a,b)
 p.write_text(s)
# Per-file edits
p=R/'LocatorArithmetic.lean'; s=p.read_text();
for a,b in [('def LA : ℕ := 100000','def LA : ℕ := 110000'),('120, 27, LB, 97, 20, LA','120, 27, LB, 102, 21, LA'),('(2 : ℕ)^43','(2 : ℕ)^44'),('(43 : ℝ)','(44 : ℝ)'),('(43 : ℕ)','(44 : ℕ)'),('13463782 131071 110000 21 98','13463782 131071 110000 21 103'),('12008238 131071 100000 19 88','12008238 131071 100000 19 92')]: s=req(s,a,b)
p.write_text(s)
p=R/'LocatorScalarArithmetic.lean'; s=p.read_text(); s=req(s,'def yTotalCap : ℕ := 61','def yTotalCap : ℕ := 62').replace('The Y+R cap is 61','The Y+R cap is 62'); p.write_text(s)
p=R/'LocatorScalar.lean'; s=p.read_text().replace('(multiplicity, Y+R cap, R cap) = (45, 61, 13)','(multiplicity, Y+R cap, R cap) = (45, 62, 13)'); p.write_text(s)
p=R/'LocatorResidual.lean'; s=p.read_text(); s=req(s,'hTcaps : T.degreeOf 1 ≤ 97 ∧ T.degreeOf 2 ≤ 20 ∧ T.degreeOf 3 ≤ 100000','hTcaps : T.degreeOf 1 ≤ 102 ∧ T.degreeOf 2 ≤ 21 ∧ T.degreeOf 3 ≤ 110000'); s=req(s,'(74 * agreements - 1) / w = 97','(74 * agreements - 1) / w = 102'); p.write_text(s)
p=R/'LocatorIrreducibleCaps.lean'; s=p.read_text()
M=[('Finset.range 51, ∑ r ∈ Finset.range 8','Finset.range 56, ∑ r ∈ Finset.range 9'),('(99954 - j - r)','(109954 - j - r)'),('Finset.range 46, ∑ r ∈ Finset.range 9','Finset.range 51, ∑ r ∈ Finset.range 10'),('(99949 - j - r)','(109949 - j - r)'),('Finset.range 43, ∑ r ∈ Finset.range 10','Finset.range 48, ∑ r ∈ Finset.range 11'),('(99946 - j - r)','(109946 - j - r)'),('Finset.range 29, ∑ r ∈ Finset.range 9','Finset.range 33, ∑ r ∈ Finset.range 10'),('have hL : 100000 - wt residualTotalWeights F ≤ 99953','have hL : 110000 - wt residualTotalWeights F ≤ 109953'),('have hL : 100000 - wt residualTotalWeights F ≤ 99948','have hL : 110000 - wt residualTotalWeights F ≤ 109948'),('have hL : 100000 - wt residualTotalWeights F ≤ 99945','have hL : 110000 - wt residualTotalWeights F ≤ 109945'),('7303458 99953 7 51','7303458 109953 8 56'),('6648102 99948 8 46','6648102 109948 9 51'),('6254888 99945 9 43','6254888 109945 10 48'),('4275059 99941 8 29','4275059 99941 9 33'),('show 7 + 1 = 8 by decide, show 99953 + 1 = 99954 by decide','show 8 + 1 = 9 by decide, show 109953 + 1 = 109954 by decide'),('show 8 + 1 = 9 by decide, show 99948 + 1 = 99949 by decide','show 9 + 1 = 10 by decide, show 109948 + 1 = 109949 by decide'),('show 9 + 1 = 10 by decide, show 99945 + 1 = 99946 by decide','show 10 + 1 = 11 by decide, show 109945 + 1 = 109946 by decide'),('show 8 + 1 = 9 by decide, show 99941 + 1 = 99942 by decide','show 9 + 1 = 10 by decide, show 99941 + 1 = 99942 by decide')]
for a,b in M: s=req(s,a,b)
p.write_text(s)
(R/'score.txt').write_text('6744\n'); (R/'radius.txt').write_text('10265855/33554432\n')
C='\n'.join(p.read_text() for p in F)
old=['ProtocolClaim 6743','80191','181953','50882','10264575','23289857','12736710','11463039','8187885','15829911','237171134622841770','274980727060991165','1050403922','localRankBound 70 100000 20','localRankBound 63 100000 18','70 * agreements','63 * agreements','100000 20 70','100000 18 63','yTotalCap : ℕ := 61']
if [x for x in old if x in C]: raise SystemExit('stale: '+str([x for x in old if x in C]))
need=['ProtocolClaim 6744 10265855 33554432','def fixedRegularCap : ℕ := 241613533669933335','def listBudget : ℕ := 1067833522','def mcaBudget : ℕ := 274980727043561565','coefficientCount 13463782 131071 110000 21','coefficientCount 12008238 131071 100000 19','coefficientCount 8187435 131071 43759 13','coefficientCount 15829041 131071 1497 27']
if [x for x in need if x not in C]: raise SystemExit('missing: '+str([x for x in need if x not in C]))
print('PATCHED 6744; exact ledger 243634911618861319 < 274980727043561565; slack 31345815424700246')
if '--build' in sys.argv:
 for c in [['bash','scripts/check-submission-imports.sh','lower','ProximityPrize/SubmissionLower'],['lake','build','ProximityPrize.SubmissionLower.Solution'],['lake','env','lean','ProximityPrize/SubmissionLower/Solution.lean']]: subprocess.run(c,check=True)

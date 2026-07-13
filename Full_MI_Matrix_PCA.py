import numpy as np, pandas as pd
from sklearn.metrics import mutual_info_score
from sklearn.preprocessing import StandardScaler
from sklearn.decomposition import PCA
df=pd.read_csv('prime_atlas_norm.csv')

feat=['chi3','chi4','chi8','CMw','CMi','CMi2','N1','N2','N3','tau']
def binv(x,nb=6): 
    q=np.quantile(x,np.linspace(0,1,nb+1)[1:-1]); return np.digitize(x,q)
B={f:binv(df[f].values) for f in feat}

print("=== MUTUAL INFORMATION matrix (normalized coords, all pairs) ===")
print(f"{'':6}"+"".join(f"{f:>6}" for f in feat))
MI=np.zeros((len(feat),len(feat)))
for i,fi in enumerate(feat):
    for j,fj in enumerate(feat):
        MI[i,j]=mutual_info_score(B[fi],B[fj])
    print(f"{fi:>6}"+"".join(f"{MI[i,j]:6.2f}" for j in range(len(feat))))

print("\n=== dependent pairs (off-diagonal MI > 0.1) ===")
for i in range(len(feat)):
    for j in range(i+1,len(feat)):
        if MI[i,j]>0.1:
            print(f"  {feat[i]} <-> {feat[j]}: MI={MI[i,j]:.3f}")
print("\n  expected: CMw<->chi3 (Z[omega]), CMi<->chi4 & CMi2<->chi4 & CMi<->CMi2 (both Z[i])")

# verify the CM<->character determinism
print("\n=== deterministic reciprocity dependences ===")
df['CMw0']=(np.abs(df['CMw'])<1e-9).astype(int)
df['CMi0']=(np.abs(df['CMi'])<1e-9).astype(int)
print(f"  CMw=0 <=> chi3=-1: {(df[df['chi3']==-1]['CMw0'].mean()==1.0) and (df[df['chi3']==1]['CMw0'].mean()==0.0)}")
print(f"  CMi=0 <=> chi4=-1: {(df[df['chi4']==-1]['CMi0'].mean()==1.0) and (df[df['chi4']==1]['CMi0'].mean()==0.0)}")
# the two Z[i] curves share supersingular primes -> should be dependent
print(f"  CMi and CMi2 both vanish at same primes (both CM by Z[i]): "
      f"{(df['CMi0']==(np.abs(df['CMi2'])<1e-9).astype(int)).mean():.3f} agreement")

# ===== PCA on the CM/character block vs the full space =====
print("\n=== PCA: effective dimension, CORRECTED ===")
def effdim(X):
    ev=PCA().fit(StandardScaler().fit_transform(X)).explained_variance_ratio_
    return np.exp(-np.sum(ev*np.log(ev+1e-12))), ev
# full space
ed_full,ev_full=effdim(df[feat].values)
print(f"  full 10-coord space: eff_dim = {ed_full:.2f} / 10")
# reciprocity block: chi3,chi4,chi8 + the 3 CM curves (should be LOW dim: CM collapse onto chars)
recip=['chi3','chi4','chi8','CMw','CMi','CMi2']
ed_r,ev_r=effdim(df[recip].values)
print(f"  reciprocity block (3 chars + 3 CM curves, 6 coords): eff_dim = {ed_r:.2f} / 6")
print(f"    variance spectrum: {[round(v,3) for v in ev_r]}")
# non-CM block: should be FULL dim (independent)
noncm=['N1','N2','N3','tau']
ed_n,ev_n=effdim(df[noncm].values)
print(f"  non-CM block (3 non-CM curves + tau, 4 coords): eff_dim = {ed_n:.2f} / 4")
print(f"    variance spectrum: {[round(v,3) for v in ev_n]}")

print("\n=== THE CORRECTED PICTURE ===")
print(f"  reciprocity block collapses: eff_dim {ed_r:.2f} < 6  (CM curves ARE their characters)")
print(f"  non-CM block fills space:    eff_dim {ed_n:.2f} ~ 4  (Sato-Tate independence)")
print(f"  => the primes have LOW-dimensional structure in reciprocity coordinates,")
print(f"     FULL-dimensional independence in non-reciprocity coordinates.")
print(f"     My raw-data eff_dim 6.98 MISSED the reciprocity collapse entirely.")

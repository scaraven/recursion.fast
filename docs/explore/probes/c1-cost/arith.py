# C1 cost arithmetic (all inputs cited in C1-cost.md section 1)
import math
ns=1e-9; us=1e-6; ms=1e-3
t_rust=2102e-6/16384; t_simd_serial=124.11*ns; t_simd_many=45.63*ns; t_lean=(151e-9,164e-9)
tree=2**22
print("t_rust per compression ns", t_rust/ns)
print("WS r8: simd-many %.0f ms, rust %.0f ms, lean %.0f-%.0f ms"%(tree*t_simd_many/ms, tree*t_rust/ms, tree*t_lean[0]/ms, tree*t_lean[1]/ms))
# spartan-chain n=2^14 verifier compressions
m=256; lN=17; t=260; leafSize=1464107; cols=260*(8*m+31*lN)
merkle=t*(math.ceil((2+8*m)/64)+lN); absorb_b=leafSize-cols-80; absorbs=3+29+29+22+2; squeezes=m+2*29+1+29+6+22+math.ceil(260/(256//17))
fs=absorb_b/64+absorbs; print("cols",cols,"merkle",merkle,"absorb bytes",absorb_b,"absorbs",absorbs,"squeezes",squeezes,"fs compr",fs)
hv_sc=merkle+fs+squeezes+1; print("spartan h_V compressions %.0f"%hv_sc, "queries", t*(1+lN)+absorbs+squeezes+1)
# D4 list hashing for a spartan-chain child: enc(q,a) = 4-byte length + q + 32-byte answer
leafq=t*(2050+36); nodeq=t*lN*(64+36); absq=absorb_b+absorbs*(35+36); sqq=squeezes*(34+36); seed=74+36
d4=(leafq+nodeq+absq+sqq+seed)/64; print("D4 list bytes %.0f -> %.0f compressions, ratio %.3f"%((leafq+nodeq+absq+sqq+seed), d4, d4/hv_sc))
print("node query ratio: 1-block real %.2f, 2-block real %.2f"%(100/64,101/128))
# deferral / concatenation at r=8
for hv in (5100,9200,10000,hv_sc):
    print("h_V=%6d: concat 256*hv=%.2fM, deferral 511*hv=%.2fM compr, ratio to WS 2^22: concat %.2f deferral %.2f; WS/deferral compression %.2f"%(hv,256*hv/1e6,511*hv/1e6,256*hv/tree,511*hv/tree,tree/(511*hv)))
# r=4 n=2^20
tree4=2**24
print("WS r4n20: simd %.0f ms rust %.0f ms lean %.0f ms"%(tree4*t_simd_many/ms,tree4*t_rust/ms,tree4*158e-9/ms))
for hv in (6400,12000,14000):
    d=31*hv; print(" r4 deferral hv=%d: %d compr = %.0f ms at 128ns; WS/def compr %.1f"%(hv,d,d*t_rust/ms,tree4/d))
print("IVC WS 2^20 serial: %.0f ms (blake2s_simd serial), %.0f ms lean"%(2**20*t_simd_serial/ms,2**20*158e-9/ms))
for k in (1,2**10,2**14,2**17):
    print(" IVC k=%6d: deferral root queries (2^20/k)*10k = %.3g, time at 128ns %.3g s; WS/def %.3g; recursion overhead h/k %.3g"%(k,2**20/k*1e4,2**20/k*1e4*t_rust,2**20/(2**20/k*1e4),1e4/k))
# charge with t_hash = T_leaf/n
Tl=7.67; n=16384
for name,hv in (("spartan per query",5156),("spartan per compression",hv_sc),("leanVM child",18420/2),("WHIR UD+FS ~",12000)):
    print("charge %s: h/n=%.3f ; per tree 510*h/n*T_leaf vs 256 T_leaf -> ratio %.2f"%(name,hv/n,510*hv/n/256))
print("t_hash: spartan n=16 %.2f ms, 1024 %.3f ms, 2^14 %.3f ms; flock devVM %.3f ms; flock M4 %.2f us"%(0.183/16/ms,0.707/1024/ms,Tl/n/ms,14.2521/16384/ms,1/485033/us))
# fixed constant charge per node vs spartan leaf
for tf in (1/485033,Tl/n):
    print("fixed t=%.3g s: per node 2*hv_sc*t = %.3g s = %.3g x T_leaf"%(tf,2*hv_sc*tf,2*hv_sc*tf/Tl))
# leanVM hash share
print("leanVM 2->1: compr 2^14.169=%.0f; at flock rate %.1f ms of 394 ms = %.1f%%"%(2**14.169,2**14.169/485033/ms,2**14.169/485033/0.394*100))
# Stwo published rows (Plonk 30 cols, Poseidon 96 cols)
pl=1189+2063+176947+51682; po=840+0+42720+120480; print("stwo rows plonk",pl,"poseidon",po,"poseidon cell share %.1f%%"%(po*96/(po*96+pl*30)*100))
# R1CS-bits node: hashing rows vs field rows
for hv,fm in ((hv_sc,3.1e7),(10000,6e5)):
    h=2*hv*2**14; f=2*fm; print("R1CS bits node: hash rows %.3g field rows %.3g share %.1f%%"%(h,f,h/(h+f)*100))
print("non-native: 3.1e7 K-mul * 4096 = %.3g rows vs hash %.3g"%(3.1e7*4096,2*hv_sc*2**14))
# prover oracle traffic per spartan-chain leaf
N=2**17; calls=N+(N-1)+absorbs+squeezes+1; comp=N*33+(N-1)+fs+squeezes; byts=N*2050+(N-1)*64+absorb_b
print("prover leaf: calls %d, compressions %.3gM, bytes %.1f MB; rate over 7.67 s: %.0f calls/s %.1f MB/s"%(calls,comp/1e6,byts/1e6,calls/Tl,byts/1e6/Tl))
print("tree leaves: calls %.3g, bytes %.1f GB"%(256*calls,256*byts/1e9))
print("table memory: full queries leaves %.1f GB; fingerprint 128B/entry x 2*256*calls = %.1f GB; WHIR-like 2^20 calls/leaf x 512 proofs x128B = %.1f GB"%(256*byts/1e9, 2*256*calls*128/1e9, 512*2**20*128/1e9))
# flat SNARK vs recursion tree work
for name,leaf,node in (("R1CS-bits (node=2*h_V/n leaves)",1.0,2*hv_sc/n),("WHIR-class",1.0,2*12000/n),("leanVM-class (Flock leaf 2^14 at 485k/s, node 0.394s)",16384/485033,0.394)):
    tw=256*leaf+255*node; print("%s: tree work %.1f vs flat %.1f -> %.2fx"%(name,tw,256*leaf,tw/(256*leaf)))
lf=2**20/485033; print("r4n20 leanVM-class: tree %.1f s flat %.1f s ratio %.2f"%(16*lf+15*0.394,16*lf,(16*lf+15*0.394)/(16*lf)))
# million chains
for nm,T in (("n=2^14 spartan",7.67),("n=16 spartan",0.183),("n=1024 spartan",0.707),("Lean P n=16",34.9),("Flock devVM 2^14",14.25),("Flock M4 2^14",16384/485033)):
    print("1e6 x %s: %.3g s = %.1f days = %.1f h"%(nm,1e6*T,1e6*T/86400,1e6*T/3600))
import statistics as st
runs=[7.61,7.43,7.98]; cv=st.stdev(runs)/st.mean(runs); print("CV spartan 2^14 %.3f"%cv)
for c in (0.03,0.037,0.063):
    for prec in (0.01,0.005):
        print(" CV %.3f precision %.3f -> N=%.0f"%(c,prec,(1.2533*c/prec)**2))
# D3 WOTS+
print("WOTS+ w16: avg %.0f worst %.0f"%(67*7.5+34+20,67*15+34+20))
print("SPHINCS per sig %.0f, XMSS per sig %.0f"%(2**16.992/245,2**16.989/900))

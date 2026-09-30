# Validate the exact (e,k) representation against direct 2-adic big-integer arithmetic.
# Target y random (M bits). Reference: z_ref(0)=y, z_ref' = (R^lam z_ref - r)/2 with r = z_ref mod 2.
# Candidate: z_p(0) = y (e=0,k=0). Random choices; z_p' = (R^d z_p - 1)/2 (odd, term) or z_p/2 (even);
# padding: if e' < 0, multiply z_p by R^{-e'} (raise its level to the line). Check z_p == R^e z_ref + k (mod 2^(M-t)).
import random
R=9; rn,rd=5,16; M=4000; random.seed(7); bad=0; steps=0
for trial in range(40):
    y=random.getrandbits(M); zr=y; zp=y; e=0; k=0
    for t in range(1500):
        mod=1<<(M-t)
        r=zr&1; lam=((t+1)*rn)//rd-(t*rn)//rd
        par=(zp)&1
        assert par==((r+k)&1), ('parity mismatch',trial,t)
        if par==0:
            zp=zp//2 if zp%2==0 else None
            e2=e-lam
            if e2<0: e2=0; zp=zp*R; k2=(r+R*k)//2
            else: k2=(R**e2*r+k)//2
        else:
            d=random.choice([1,1,1,2,2,3])
            zp=(R**d*zp-1)//2
            e2=e+d-lam; k2=(R**e2*r+R**d*k-1)//2
        zr=(R**lam*zr-r)//2
        e,k=e2,k2
        m2=1<<(M-t-1)
        if (zp-(R**e*zr+k))%m2!=0: bad+=1; print('MISMATCH',trial,t,e,k); break
        steps+=1
print('checked steps:',steps,' mismatches:',bad)

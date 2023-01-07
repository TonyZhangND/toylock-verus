#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus!{

spec fn fibo(n: nat) -> nat 
{
    decreases(n);
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibo((n-2) as nat) + fibo((n-1) as nat)
    }
}

proof fn lemma_fibo_is_monotonic(i:nat, j:nat) 
    requires i <= j
    ensures fibo(i) <= fibo(j)
    decreases j - i
{
    if i == j {
        assert(fibo(i) == fibo(j));
    } else if i == j - 1 {
        reveal_with_fuel(fibo, 2);
        lemma_fibo_is_monotonic(i, (j-1) as nat);
    } else {
        lemma_fibo_is_monotonic(i, (j-1) as nat);
        lemma_fibo_is_monotonic(i, (j-2) as nat);
    }
}

spec fn fibo_fits_u64(n: nat) -> bool {
    fibo(n) <= 0xffff_ffff_ffff_ffff
}

fn fibo_impl(n: u64) -> (res: u64)
    requires fibo_fits_u64(n as nat)
    ensures res == fibo(n as nat)
{
    if n == 0 {
        return 0
    }
    let mut prev:u64 = 0;
    let mut curr:u64 = 1;
    let mut i:u64 = 1;
    while i < n 
        invariant
            0 < i && i <= n,
            fibo_fits_u64(n as nat),
            fibo_fits_u64(i as nat),
            curr == fibo(i as nat),
            prev == fibo((i-1) as nat),
    {
        i = i + 1;
        proof {
            lemma_fibo_is_monotonic(i as nat, n as nat);
        }
        let new_curr = prev + curr;
        prev = curr;
        curr = new_curr;
    }
    return curr;
}

fn main(){}

} // verus!
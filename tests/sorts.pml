// Sort definitions
sort v = ι
sort t = τ
sort s = σ

sort w = ι → (τ → ο)
sort y = ι → ι → ι
sort z = (ι → ι) → ι
sort c = (v → w) → ο → κ
sort l = ι → κ
sort m = <term> → (<term> → <term>)

def unit : ι = {}
def reco  : ι = {l1 = {}, l2 = {}}
def unit_v : v = {}

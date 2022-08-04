include lib.order
include lib.list
include lib.list_sorted
include lib.list_count

// Specification of a sorting algorithm.

type sorting_algorithm =
  ∃sort_fun,
    { sort_fun   : sort_fun ∈ (∀a, total_order⟨a⟩ ⇒ list⟨a⟩ ⇒ list⟨a⟩)
    ; sort_sorts : ∀a, ∀o∈total_order⟨a⟩, ∀l∈list⟨a⟩, sorted o (sort_fun o l)
    ; sort_count : ∀a, ∀o∈total_order⟨a⟩, ∀e∈a, ∀l∈list⟨a⟩,
                     count o e l ≡ count o e (sort_fun o l) }

// Insertion sort.

include lib.list_insert_sort

val insert_sort : sorting_algorithm =
  { sort_fun   = isort
  , sort_sorts = isort_sorts
  , sort_count = isort_count }

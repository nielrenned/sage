import sage.rings.ring as ring

from sage.rings.padics.witt_ring import WittRing_p_typical
from sage.rings.padics.witt_ring import WittRing_finite_field
from sage.rings.padics.witt_ring import WittRing_p_invertible
from sage.rings.padics.witt_ring import WittRing_non_p_typical
from sage.rings.padics.witt_ring import WittRing_integers
from sage.rings.padics.witt_ring import WittRing_integers_mod_power_of_p

from sage.categories.commutative_rings import CommutativeRings
from sage.rings.abc import IntegerModRing
from sage.sets.primes import Primes
from sage.rings.integer_ring import ZZ

from sage.rings.finite_rings.finite_field_base import is_FiniteField

_CommutativeRings = CommutativeRings()
_Primes = Primes()


def WittRing(base_ring, prec=1, p=None, algorithm='auto'):
    r"""
    Return the ring of Witt vectors over the given ring.

    INPUT:

    - ``base_ring`` -- commutative ring; the ring whose elements will be
      the components of the Witt vectors.

    - ``prec`` -- integer (default: `1`); length of the Witt vectors
    
    - ``p`` -- prime number (default: `None`); the prime that specifies
      the formulas for the sum and product polynomials. If None, the 
      characteristic of `base_ring` is used.
    
    - ``algorithm`` -- string (default: "auto"); the algorithm to use to
      calculate sums and products. The options are "none", "auto", "standard",
      and "finotti".

    OUTPUT: the ring of Witt vectors over the specified base ring

    EXAMPLES:

    We can construct the ring of Witt vectors over finite fields. ::

        sage: R = WittRing(GF(5^3), 3)
        sage: R
        Ring of Witt Vectors of length 3 over Finite Field in z3 of size 5^3
        sage: R.random_element() # random
        (2, 2*z3^2 + z3 + 4, 2*z3^2 + z3 + 1)

    This is isomorphic to the unique unramified extension of Z_5 of degree 3.
    In fact, for speed, this isomorphism is how the computations are done. ::

        sage: R._algorithm
        'Zq_isomorphism'

    If we instead wanted to use the standard algorithm, i.e. the Witt sum
    and product polynomials, we can specify the `algorithm` argument ::

        sage: S = WittRing(GF(5^3), 3, algorithm='standard')
        sage: S
        Ring of Witt Vectors of length 3 over Finite Field in z3 of size 5^3
    
    In fact, we can construct the ring of Witt vectors over any commutative
    ring. In this case, we need to specify a prime, as the characteristic
    of \\ZZ is not prime. ::
    
        sage: R = WittRing(ZZ, 5, p=3)
        sage: R
        Ring of 3-Witt Vectors of length 5 over Integer Ring
        sage: R.random_element() # random
        (0, -3, -1, -1, 0)

    TESTS:
    
    Test basic rings::

        sage: R = WittRing(GF(5), 10)
        sage: R
        Ring of Witt Vectors of length 10 over Finite Field of size 5
        sage: R._algorithm
        'Zq_isomorphism'
        sage: R(list(range(10))) + R(list(range(0,20,2)))
        (0, 3, 4, 0, 1, 4, 2, 2, 1, 3)
        sage: R(list(range(10))) * R(list(range(0,20,2)))
        (0, 0, 2, 3, 1, 1, 4, 3, 1, 4)
    
    Test algorithm decision making::
    
        sage: R = WittRing(GF(7), 10)
        sage: type(R)
        <class 'sage.rings.padics.witt_ring.WittRing_finite_field_with_category'>
        sage: R._algorithm
        'Zq_isomorphism'
        sage: R = WittRing(GF(7), 3, algorithm='standard')
        sage: type(R)
        <class 'sage.rings.padics.witt_ring.WittRing_p_typical_with_category'>
        sage: R = WittRing(GF(7).algebraic_closure(), 4)
        sage: type(R)
        <class 'sage.rings.padics.witt_ring.WittRing_p_typical_with_category'>
        sage: R._algorithm
        'finotti'
        sage: R = WittRing(Zmod(27), 5, p=3)
        sage: R
        Ring of 3-Witt Vectors of length 5 over Ring of integers modulo 27
        sage: R._algorithm
        'IntegerMod_isomorphism'
        sage: R = WittRing(Zmod(25), 5, p=3)
        sage: R
        Ring of 3-Witt Vectors of length 5 over Ring of integers modulo 25
        sage: R._algorithm
        'standard_otf'
    """
    
    # Handle as many error cases up front as possible.
    if not ring.is_Ring(base_ring):
        raise TypeError(f'Base ring {base_ring} must be a ring.')
    
    if base_ring not in _CommutativeRings:
        raise TypeError(
            f'Cannot create Ring of Witt Vectors over {base_ring}: '
            f'{base_ring} is not a commutative ring.'
        )
    
    char = base_ring.characteristic()
    if p is None and char not in _Primes:
        raise ValueError(
            f'Cannot create Ring of Witt Vectors over {base_ring}: '
            f'{base_ring} has non-prime characteristic and '
             'no prime was supplied.'
        )
    if p is not None and p not in _Primes:
        raise ValueError(
            f'Cannot create Ring of {p}-Witt Vectors: {p} is not a prime.'
        )
    
    if algorithm not in [None, 'none', 'auto', 'standard', 'finotti']:
        raise ValueError(
            f"'{algorithm}' is not a valid algorithm. "
             "It must be one of 'none', 'auto', 'standard', or 'finotti'."
        )
    
    if algorithm is None: algorithm = 'none'
    
    prime = char if p is None else p
    if prime != char and algorithm == 'finotti':
        raise ValueError(
            f"The 'finotti' algorithm only works for p-typical Witt Rings. "
            f"The prime supplied, {p}, does not match the characteristic of "
            f"{base_ring}, {char}."
        )
    
    category = _CommutativeRings
    
    # At this point, we should have valid input.
    
    # Prefer using algorithm specified by user.
    if algorithm != 'auto' and prime == char:
        return WittRing_p_typical(base_ring, prec, prime, 
                                  algorithm=algorithm, category=category)
    
    if algorithm != 'auto' and prime != char:
        return WittRing_non_p_typical(base_ring, prec, prime, 
                                      algorithm=algorithm, category=category)
    
    # Now we know algorithm == 'auto', so we can check for special cases.
    
    # Check for the two p-typical cases
    if prime == char:
        if base_ring.is_field() and base_ring.is_finite():
            # Check to see if we have something like Zmod(p).
            # In that case, we need to convert it to the FiniteField
            # class, otherwise certain method calls will fail.
            if not is_FiniteField(base_ring): base_ring = base_ring.field()
                
            return WittRing_finite_field(base_ring, prec, prime,
                                         category=category)
        
        return WittRing_p_typical(base_ring, prec, prime,
                                  algorithm='finotti', category=category)
    
    # Check for all the non-p-typical cases
    
    if base_ring(prime).is_unit():
        return WittRing_p_invertible(base_ring, prec, prime, category=category)
    
    if base_ring == ZZ:
        return WittRing_integers(prec, prime, category=category)
    
    alpha = ZZ.valuation(prime)(char)
    if isinstance(base_ring, IntegerModRing) and prime**alpha == char:
        return WittRing_integers_mod_power_of_p(base_ring, prec, prime,
                                                category=category)
        
    return WittRing_non_p_typical(base_ring, prec, prime,
                                  algorithm='standard',
                                  category=category)
        

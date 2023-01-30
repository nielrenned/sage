import sage.rings.ring as ring

from sage.rings.padics.witt_ring import WittRing_p_typical
from sage.rings.padics.witt_ring import WittRing_finite_field
from sage.rings.padics.witt_ring import WittRing_p_invertible
from sage.rings.padics.witt_ring import WittRing_non_p_typical
from sage.rings.padics.witt_ring import WittRing_integers_mod_power_of_p

from sage.categories.commutative_rings import CommutativeRings
from sage.rings.abc import IntegerModRing
from sage.sets.primes import Primes
from sage.rings.integer_ring import ZZ

from sage.rings.finite_rings.finite_field_base import is_FiniteField

_CommutativeRings = CommutativeRings()
_Primes = Primes()


def WittRing(base_ring, prec=1, p=None, algorithm='auto'):
    
    if not ring.is_Ring(base_ring):
        raise TypeError(f'Base ring {base_ring} must be a ring.')
    
    if base_ring not in _CommutativeRings:
        raise TypeError(f'Cannot create Ring of Witt Vectors over {base_ring}: {base_ring} is not a commutative ring.')
    
    char = base_ring.characteristic()
    prime = None
    if p is None:
        if char not in _Primes:
            raise ValueError(f'Cannot create Ring of Witt Vectors over {base_ring}: {base_ring} has non-prime characteristic and no prime was supplied.')
        else:
            prime = char
    elif p in _Primes:
        prime = p
    else:
        raise ValueError(f'Cannot create Ring of {p}-Witt Vectors: {p} is not a prime.')
    
    if algorithm is None:
        algorithm = 'none'
    elif algorithm not in ['none', 'auto', 'standard', 'finotti']:
        raise ValueError(f"'{algorithm}' is not a valid algorithm. It must be one of 'none', 'auto', 'standard', or 'finotti'.")
    
    if prime == char: # p-typical
        if base_ring.is_field() and base_ring.is_finite():
            if not is_FiniteField(base_ring):
                # This means we have something like Zmod(p)
                base_ring = base_ring.field()
            
            # TODO: document that this ignores the choice of algorithm
            return WittRing_finite_field(base_ring, prec, prime,
                                         category=_CommutativeRings)
        else:
            if algorithm == 'auto':
                algorithm = 'finotti'
            return WittRing_p_typical(base_ring, prec, prime,
                                      algorithm=algorithm,
                                      category=_CommutativeRings)
    else: # non-p-typical
        if algorithm == 'finotti':
            raise ValueError(f"The 'finotti' algorithm only works for p-typical Witt Rings.")
        if base_ring(prime).is_unit():
            # TODO: document that this ignores the choice of algorithm
            return WittRing_p_invertible(base_ring, prec, prime,
                                         category=_CommutativeRings)
        elif (
            isinstance(base_ring, IntegerModRing) and \
            p**(ZZ.valuation(p)(char)) == char
        ):
            return WittRing_integers_mod_power_of_p(
                base_ring, prec, prime,
                category=_CommutativeRings
            )
        else:
            if algorithm == 'auto':
                algorithm = 'standard'
            return WittRing_non_p_typical(base_ring, prec, prime,
                                          algorithm=algorithm,
                                          category=_CommutativeRings)

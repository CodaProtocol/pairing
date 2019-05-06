use super::fq::{Fq, FROBENIUS_COEFF_FQ3_C1, NEGATIVE_ONE};
use ff::{Field, SqrtField};
use rand::{Rand, Rng};

use std::cmp::Ordering;

/// An element of Fq3, represented by c0 + c1 * v + c2 * v^(2).
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Fq3 {
    pub c0: Fq,
    pub c1: Fq,
    pub c2: Fq,
}

impl ::std::fmt::Display for Fq3 {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fq3({} + {} * v, {} * v^2)", self.c0, self.c1, self.c2)
    }
}

/// `Fq3` elements are ordered lexicographically.
impl Ord for Fq3 {
    #[inline(always)]
    fn cmp(&self, other: &Fq3) -> Ordering {
        match self.c2.cmp(&other.c2) {
            Ordering::Greater => Ordering::Greater,
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.c1.cmp(&other.c1),
        }
    }
}

impl PartialOrd for Fq3 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fq3) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Fq3 {
    /// Multiply by quadratic nonresidue v.
    // // nonresidue * c2, c0, c1
    pub fn mul_by_nonresidue(&mut self) {
        use std::mem::swap;
        swap(&mut self.c0, &mut self.c1);
        swap(&mut self.c0, &mut self.c2);
        self.c0.mul_by_nonresidue();
    }

    /// Norm of Fq3 as extension field in i over Fq
    // TODO double check formula
    pub fn norm(&self) -> Fq {
        let mut t0 = self.c0;
        let mut t1 = self.c1;
        t0.square();
        t1.square();
        t1.add_assign(&t0);

        t1
    }
}

impl Rand for Fq3 {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        Fq3 {
            c0: rng.gen(),
            c1: rng.gen(),
            c2: rng.gen(),
        }
    }
}

impl Field for Fq3 {
    fn zero() -> Self {
        Fq3 {
            c0: Fq::zero(),
            c1: Fq::zero(),
            c2: Fq::zero(),
        }
    }

    fn one() -> Self {
        Fq3 {
            c0: Fq::one(),
            c1: Fq::zero(),
            c2: Fq::zero(),
        }
    }

    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero()
    }

    fn double(&mut self) {
        self.c0.double();
        self.c1.double();
        self.c2.double();
    }

    fn negate(&mut self) {
        self.c0.negate();
        self.c1.negate();
        self.c2.negate();
    }

    fn add_assign(&mut self, other: &Self) {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);
        self.c2.add_assign(&other.c2);
    }

    fn sub_assign(&mut self, other: &Self) {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
        self.c2.sub_assign(&other.c2);
    }

    // TODO: change this
    fn frobenius_map(&mut self, power: usize) {
        self.c0.frobenius_map(power);
        self.c1.frobenius_map(power);
        self.c2.frobenius_map(power);

        self.c1.mul_assign(&FROBENIUS_COEFF_FQ3_C1[power % 3]);
        self.c2.mul_assign(&FROBENIUS_COEFF_FQ3_C1[power % 3]);
    }

    /* from https://github.com/scipr-lab/libff/blob/f2067162520f91438b44e71a2cab2362f1c3cab4/libff/algebra/fields/fp3.tcc#L100
    Devegili OhEig Scott Dahab --- Multiplication and Squaring on Pairing-Friendly Fields.pdf; Section 4 (CH-SQR2) */
    fn square(&mut self) {
        let mut s0 = self.c0;
        s0.square();
        let mut ab = self.c0;
        ab.mul_assign(&self.c1);
        let mut s1 = ab;
        s1.double();
        let mut s2 = self.c0;
        s2.sub_assign(&self.c1);
        s2.add_assign(&self.c2);
        s2.square();
        let mut bc = self.c1;
        bc.mul_assign(&self.c2);
        let mut s3 = bc;
        s3.double();
        let mut s4 = self.c2;
        s4.square();

        // return c0 = s0 + non_residue * s3,
        self.c0 = s3;
        self.c0.mul_by_nonresidue();
        self.c0.add_assign(&s0);

        // return c1 = s1 + non_residue * s4,
        self.c1 = s4;
        self.c1.mul_by_nonresidue();
        self.c1.add_assign(&s1);

        // return c2 = s1 + s2 + s3 - s0 - s4);
        self.c2 = s1;
        self.c2.add_assign(&s2);
        self.c2.add_assign(&s3);
        self.c2.sub_assign(&s0);
        self.c2.sub_assign(&s4);
    }

    fn mul_assign(&mut self, other: &Self) {
        let mut a_a = self.c0;
        let mut b_b = self.c1;
        let mut c_c = self.c2;
        a_a.mul_assign(&other.c0);
        b_b.mul_assign(&other.c1);
        c_c.mul_assign(&other.c2);

        // aA + non_residue * ( (b + c) * (B + C) - bB - cC )
        let mut t1 = other.c1;
        t1.add_assign(&other.c2);
        {
            let mut tmp = self.c1;
            tmp.add_assign(&self.c2);

            t1.mul_assign(&tmp);
            t1.sub_assign(&b_b);
            t1.sub_assign(&c_c);
            t1.mul_by_nonresidue();
            t1.add_assign(&a_a);
        }

        // (a + c) * (A + C) - aA + bB - cC
        let mut t3 = other.c0;
        t3.add_assign(&other.c2);
        {
            let mut tmp = self.c0;
            tmp.add_assign(&self.c2);

            t3.mul_assign(&tmp);
            t3.sub_assign(&a_a);
            t3.add_assign(&b_b);
            t3.sub_assign(&c_c);
        }

        // (a + b) * (A + B) - aA - bB + non_residue * cC
        let mut t2 = other.c0;
        t2.add_assign(&other.c1);
        {
            let mut tmp = self.c0;
            tmp.add_assign(&self.c1);

            t2.mul_assign(&tmp);
            t2.sub_assign(&a_a);
            t2.sub_assign(&b_b);
            c_c.mul_by_nonresidue();
            t2.add_assign(&c_c);
        }

        self.c0 = t1;
        self.c1 = t2;
        self.c2 = t3;
    }

    // from https://github.com/scipr-lab/libff/blob/f2067162520f91438b44e71a2cab2362f1c3cab4/libff/algebra/fields/fp3.tcc#L119
    /* From "High-Speed Software Implementation of the Optimal Ate Pairing over Barreto-Naehrig Curves"; Algorithm 17 */
    fn inverse(&self) -> Option<Self> {
        let mut t0 = self.c0;
        t0.square();
        let mut t1 = self.c1;
        t1.square();
        let mut t2 = self.c2;
        t2.square();
        let mut t3 = self.c0;
        t3.mul_assign(&self.c1);
        let mut t4 = self.c0;
        t4.mul_assign(&self.c2);
        let mut t5 = self.c1;
        t5.mul_assign(&self.c2);
        // c0 = t0 - non_residue * t5
        t5.mul_by_nonresidue();
        t0.sub_assign(&t5);
        // c1 = non_residue * t2 - t3
        t2.mul_by_nonresidue();
        t2.sub_assign(&t3);
        // c2 = t1 - t4
        t1.sub_assign(&t4);

        let mut ac = self.c0;
        ac.mul_assign(&t0);
        let mut bc = self.c1;
        bc.mul_assign(&t1);
        let mut cc = self.c2;
        cc.mul_assign(&t2);
        cc.add_assign(&bc);
        cc.mul_by_nonresidue();
        cc.add_assign(&ac);

        match cc.inverse() {
            Some(t) => {
                let mut tmp = Fq3 {
                    c0: t,
                    c1: t,
                    c2: t,
                };
                tmp.c0.mul_assign(&t0);
                tmp.c1.mul_assign(&t2);
                tmp.c2.mul_assign(&t1);

                Some(tmp)
            }
            None => None,
        }
    }
}

impl SqrtField for Fq3 {
    fn legendre(&self) -> ::ff::LegendreSymbol {
        self.norm().legendre()
    }

    fn sqrt(&self) -> Option<Self> {
        if self.is_zero() {
            Some(Self::zero())
        } else {
            // a1 = self^((q - 3) / 4)
            let mut a1 = self.pow([
                0xe2c59929b0000000,
                0xadd132d14bb8ebbb,
                0xb435f11b70ab2b08,
                0xcdfc17b69413ed06,
                0xf62c89cb014d7a89,
                0x98f7ddc9d3384269,
                0xb0ca62e76e405e9,
                0xe862b3a150e0886b,
                0xeac3c2b4abec77ea,
                0xabffacf843b5daa0,
                0x3ea43d8c3d85,
                0x0,
            ]);
            let mut alpha = a1;
            alpha.square();
            alpha.mul_assign(self);
            let mut a0 = alpha;
            a0.frobenius_map(1);
            a0.mul_assign(&alpha);

            let neg1 = Fq3 {
                c0: NEGATIVE_ONE,
                c1: Fq::zero(),
                c2: Fq::zero(),
            };
            if a0 == neg1 {
                None
            } else {
                a1.mul_assign(self);
                if alpha == neg1 {
                    a1.mul_assign(&Fq3 {
                        c0: Fq::zero(),
                        c1: Fq::one(),
                        c2: Fq::zero(),
                    });
                } else {
                    alpha.add_assign(&Fq3::one());
                    // alpha = alpha^((q - 1) / 2)
                    alpha = alpha.pow([
                        0xec83bb7120000000,
                        0x73e0cc8b87d09d27,
                        0xcd794b67a0721cb0,
                        0x33fd652462b7f359,
                        0xa41db13200de51b1,
                        0x10a53e868cd02c46,
                        0xb2086ec9a49803f1,
                        0xf041cd1635eb059c,
                        0xf1d7d7231d484ff1,
                        0x72aa73502d23e715,
                        0x29c2d3b2d3ae,
                        0x0,
                    ]);
                    a1.mul_assign(&alpha);
                }
                Some(a1)
            }
        }
    }
}

#[cfg(test)]
use rand::{SeedableRng, XorShiftRng};

#[test]
fn test_fq3_mul_nonresidue() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let nqr = Fq3 {
        c0: Fq::zero(),
        c1: Fq::one(),
        c2: Fq::zero(),
    };

    for _ in 0..1000 {
        let mut a = Fq3::rand(&mut rng);
        let mut b = a;
        a.mul_by_nonresidue();
        b.mul_assign(&nqr);

        assert_eq!(a, b);
    }
}

#[test]
fn test_fq3_mul_by_1() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        let c1 = Fq::rand(&mut rng);
        let mut a = Fq3::rand(&mut rng);
        let mut b = a;

        a.mul_by_1(&c1);
        b.mul_assign(&Fq3 {
            c0: Fq::zero(),
            c1: c1,
            c2: Fq::zero(),
        });

        assert_eq!(a, b);
    }
}

#[test]
fn test_fq3_mul_by_01() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        let c0 = Fq::rand(&mut rng);
        let c1 = Fq::rand(&mut rng);
        let mut a = Fq3::rand(&mut rng);
        let mut b = a;

        a.mul_by_01(&c0, &c1);
        b.mul_assign(&Fq3 {
            c0: c0,
            c1: c1,
            c2: Fq::zero(),
        });

        assert_eq!(a, b);
    }
}

#[test]
fn fq3_field_tests() {
    use ff::PrimeField;

    ::tests::field::random_field_tests::<Fq3>();
    ::tests::field::random_frobenius_tests::<Fq3, _>(super::fq::Fq::char(), 13);
}

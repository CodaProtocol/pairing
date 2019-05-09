// MNT4-753 has twist field Fq2
use super::fq2::Fq2;
use ff::{Field, PrimeField, PrimeFieldDecodingError, PrimeFieldRepr};

// A coefficient of MNT4-753 curve, 2.
pub const A_COEFF: Fq = Fq(FqRepr([
    3553860551672651396,
    2565472393707818253,
    3424927325234966109,
    17487811826058095619,
    15730291918544907998,
    4332070408724822737,
    7212646118208244402,
    12904649141092619460,
    9289117987390442562,
    2254330573517213976,
    3065472942259520298,
    271095073719429,
]));

// B coefficient of MNT4-753 curve, 28798803903456388891410036793299405764940372360099938340752576406393880372126970068421383312482853541572780087363938442377933706865252053507077543420534380486492786626556269083255657125025963825610840222568694137138741554679540
pub const B_COEFF: Fq = Fq(FqRepr([
    2672638521926201442,
    17587766986973859626,
    1309143029066506763,
    1756412671449422902,
    5395165286423163724,
    589638022240022974,
    7360845090332416697,
    9829497896347590557,
    9341553552113883496,
    5888515763059971584,
    10173739464651404689,
    456607542322059,
]));

// Generator of G1
// X = 23803503838482697364219212396100314255266282256287758532210460958670711284501374254909249084643549104668878996224193897061976788052185662569738774028756446662400954817676947337090686257134874703224133183061214213216866019444443,
// Y = 21091012152938225813050540665280291929032924333518476279110711148670464794818544820522390295209715531901248676888544060590943737249563733104806697968779796610374994498702698840169538725164956072726942500665132927942037078135054,
// Z = 1.
pub const G1_GENERATOR_X: Fq = Fq(FqRepr([
    8680369219962409717,
    12497683146525997170,
    15236963532390397985,
    105054743605190980,
    11580223711797947725,
    5964558218084543687,
    1974179831852844611,
    13386218610606908614,
    9905737029079781539,
    3769381095189112747,
    1226496298859043045,
    409264833279765,
]));
pub const G1_GENERATOR_Y: Fq = Fq(FqRepr([
    8458069647833709466,
    16863815841372543189,
    7230518365128572001,
    17250077086581959530,
    15519583030873909149,
    3465247978511199450,
    5738818931561455055,
    12688417287395938373,
    3681991682605141223,
    10698656566578986929,
    10160396483421745615,
    127251255182962,
]));

// A coefficient of MNT4-753 G2 = mnt4753_twist_coeff_a
// mnt4753_Fq2::non_residue = mnt4753_Fq("13");
//  = (G1_A_COEFF * NON_RESIDUE, ZERO) = (26, 0)
pub const G2_A_COEFF_C0: Fq = Fq(FqRepr([
    16948538951764659373,
    10775354577659735631,
    12766795894854242596,
    8684022258823474090,
    973489465296612807,
    3883945490221946200,
    16178634811223492029,
    16155746945640075033,
    17642042187059426365,
    10295720303844380352,
    13265853240981244259,
    39422991244875,
]));
pub const G2_A_COEFF: Fq2 = Fq2 {
    c0: G2_A_COEFF_C0,
    c1: Fq(FqRepr([
        0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
};

// B coefficient of MNT4-753 G2 = mnt4753_twist_coeff_b
//  = (ZERO, G1_B_COEFF * NON_RESIDUE);
pub const G2_B_COEFF_C1: Fq = Fq(FqRepr([
    15129916544657421551,
    11332543254671606602,
    11913830318987286849,
    13905314883394440110,
    16479690325073358448,
    14869098639251228898,
    10663986895980443550,
    10768989312009479656,
    9469728929095040349,
    4512954369775881939,
    8788997129423430122,
    459763387588954,
]));
pub const G2_B_COEFF: Fq2 = Fq2 {
    c0: Fq(FqRepr([
        0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    ])),
    c1: G2_B_COEFF_C1,
};

// Generator of G2
// These are two Fq elements each because X and Y (and Z) are elements of Fq^2
// X = 22367666623321080720060256844679369841450849258634485122226826668687008928557241162389052587294939105987791589807198701072089850184203060629036090027206884547397819080026926412256978135536735656049173059573120822105654153939204,
// 19674349354065582663569886390557105215375764356464013910804136534831880915742161945711267871023918136941472003751075703860943205026648847064247080124670799190998395234694182621794580160576822167228187443851233972049521455293042,
// Y = 6945425020677398967988875731588951175743495235863391886533295045397037605326535330657361771765903175481062759367498970743022872494546449436815843306838794729313050998681159000579427733029709987073254733976366326071957733646574,
// 17406100775489352738678485154027036191618283163679980195193677896785273172506466216232026037788788436442188057889820014276378772936042638717710384987239430912364681046070625200474931975266875995282055499803236813013874788622488,
// Z = 1.
pub const G2_GENERATOR_X_C0: Fq = Fq(FqRepr([
    6027998872234822269,
    18316510890646896372,
    12312422472129155053,
    5734876120361342991,
    15269557702005117850,
    2881476951079071365,
    18286169900244335081,
    9121647201144159462,
    10143201970379789827,
    8274325828999741070,
    16324620334829045351,
    206265970291999,
]));
pub const G2_GENERATOR_X_C1: Fq = Fq(FqRepr([
    8103915349469236029,
    3264578743345366807,
    11420369645465736410,
    1082524563485784168,
    9521451516267963565,
    947729167637853217,
    980516398344887244,
    9338197375178553870,
    12279316873997193841,
    7682952744956285803,
    5880726343431033740,
    393937351760210,
]));
pub const G2_GENERATOR_Y_C0: Fq = Fq(FqRepr([
    9473954153981524211,
    17210941273038840246,
    7908789794149338247,
    14886051892012552213,
    15661744656776151922,
    12925231519316918877,
    8556358774098608262,
    12018580250090935208,
    12085312901555144792,
    16429889710969777184,
    9875783130742037645,
    390595340749132,
]));
pub const G2_GENERATOR_Y_C1: Fq = Fq(FqRepr([
    1961701679311783916,
    14701334664186945036,
    4897259467765012901,
    9133165644380234616,
    5806216571361183036,
    15854960112739074469,
    3305583651306700066,
    3531430907605494499,
    7284796601341566706,
    3173472022185515256,
    1610147509686374719,
    280032154091959,
]));

pub const FROBENIUS_COEFF_0: Fq = Fq(FqRepr([
    11000302312691101506,
    10506108233708684934,
    10935835699472258862,
    8743905913029047809,
    17088517996127229807,
    2166035204362411368,
    3606323059104122201,
    6452324570546309730,
    4644558993695221281,
    1127165286758606988,
    10756108507984535957,
    135547536859714,
]));
pub const FROBENIUS_COEFF_1: Fq = Fq(FqRepr([
    2732208433323581659,
    2172983777736624684,
    14351170316343013496,
    6345300643186282385,
    3197292113538174065,
    1887663496013421009,
    16627860175048929982,
    1842296636815120666,
    13463717484107308085,
    721000253033730237,
    1214767992212094798,
    163570781165682,
]));
pub const FROBENIUS_COEFF_2: Fq = Fq(FqRepr([
    14260497802974073023,
    5895249896161266456,
    14682908860938702530,
    17222385991615618722,
    14621060510943733448,
    10594887362868996148,
    7477357615964975684,
    12570239403004322603,
    2180620924574446161,
    12129628062772479841,
    8853285699251153944,
    362282887012814,
]));
pub const FROBENIUS_COEFF_3: Fq = Fq(FqRepr([
    6563525401674979703,
    9648071681462872351,
    10166450561757179616,
    7389527470854848093,
    2676977607417428815,
    7443018887958599516,
    7378626344463925755,
    528173014263963525,
    17146695529966638527,
    11028878272126731592,
    13672105692407504374,
    203603601378698,
]));

// Coefficients for the Frobenius automorphism.
//    1,
//    "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689600"
pub const FROBENIUS_COEFF_FQ2_C1: [Fq; 2] = [FROBENIUS_COEFF_0, FROBENIUS_COEFF_2];

// 1,
// "18691656569803771296244054523431852464958959799019013859007259692542121208304602539555350517075508287829753932558576476751900235650227380562700444433662761577027341858128610410779088384480737679672900770810745291515010467307990",
// "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689600",
//  "23206834398115182106100160267808784663211750120934935212776243228483231604266504233503543246714830633588317039329677309362453490879357004638891167538350364891904062489821230132228897943262725174047727280881395973788104254381611"
pub const FROBENIUS_COEFF_FQ4_C1: [Fq; 4] = [
    FROBENIUS_COEFF_0,
    FROBENIUS_COEFF_1,
    FROBENIUS_COEFF_2,
    FROBENIUS_COEFF_3,
];

#[derive(PrimeField)]
#[PrimeFieldModulus = "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689601"]
#[PrimeFieldGenerator = "17"]
pub struct Fq(FqRepr);

// This is negative one wrt the limbs, mod q
// -((2**756) mod q) mod q
pub const NEGATIVE_ONE: Fq = Fq(FqRepr([
    14260497802974073023,
    5895249896161266456,
    14682908860938702530,
    17222385991615618722,
    14621060510943733448,
    10594887362868996148,
    7477357615964975684,
    12570239403004322603,
    2180620924574446161,
    12129628062772479841,
    8853285699251153944,
    362282887012814,
]));

#[test]
fn test_a_coeff() {
    assert_eq!(Fq::from_repr(FqRepr::from(2)).unwrap(), A_COEFF);
}

fn print_repr(name: &str, s: &str) {
    let x = Fq::from_str(s).unwrap();
    match x {
        Fq(FqRepr(a)) => println!(
            "pub const {} : Fq = Fq(FqRepr([{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}]));",
            name, a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11]
        ),
    }
}

#[test]
fn test_b_coeff() {
    /*
    print_repr("G1_GENERATOR_X", "23803503838482697364219212396100314255266282256287758532210460958670711284501374254909249084643549104668878996224193897061976788052185662569738774028756446662400954817676947337090686257134874703224133183061214213216866019444443");
    print_repr("G1_GENERATOR_Y", "21091012152938225813050540665280291929032924333518476279110711148670464794818544820522390295209715531901248676888544060590943737249563733104806697968779796610374994498702698840169538725164956072726942500665132927942037078135054");
    print_repr("G2_A_COEFF_C0", "26");
    print_repr("G2_A_COEFF_C1", "0");

    print_repr("G2_B_COEFF_C0", "0");
    print_repr("G2_B_COEFF_C1", "39196523001581428369576759982967177918859161321667605855515469914917622337081756705006832951954384669101573360625169461998308377011601613979275218690841934572954991361632773738259652003389826903175898479855893660378722437317212");

    print_repr("G2_GENERATOR_X_C0", "22367666623321080720060256844679369841450849258634485122226826668687008928557241162389052587294939105987791589807198701072089850184203060629036090027206884547397819080026926412256978135536735656049173059573120822105654153939204");
    print_repr("G2_GENERATOR_X_C1", "19674349354065582663569886390557105215375764356464013910804136534831880915742161945711267871023918136941472003751075703860943205026648847064247080124670799190998395234694182621794580160576822167228187443851233972049521455293042");
    print_repr("G2_GENERATOR_Y_C0", "6945425020677398967988875731588951175743495235863391886533295045397037605326535330657361771765903175481062759367498970743022872494546449436815843306838794729313050998681159000579427733029709987073254733976366326071957733646574");
    print_repr("G2_GENERATOR_Y_C1", "17406100775489352738678485154027036191618283163679980195193677896785273172506466216232026037788788436442188057889820014276378772936042638717710384987239430912364681046070625200474931975266875995282055499803236813013874788622488");

    print_repr("FROBENIUS_COEFF_0", "1");
    print_repr("FROBENIUS_COEFF_1", "18691656569803771296244054523431852464958959799019013859007259692542121208304602539555350517075508287829753932558576476751900235650227380562700444433662761577027341858128610410779088384480737679672900770810745291515010467307990");
    print_repr("FROBENIUS_COEFF_2", "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689600");
    print_repr("FROBENIUS_COEFF_3", "23206834398115182106100160267808784663211750120934935212776243228483231604266504233503543246714830633588317039329677309362453490879357004638891167538350364891904062489821230132228897943262725174047727280881395973788104254381611");

    print_repr("NEGATIVE_ONE", "41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888253786114353726529584385201591605722013126468931404347949840543007986327743462853720628051692141265303114721689600");
    */

    assert_eq!(Fq::from_str("28798803903456388891410036793299405764940372360099938340752576406393880372126970068421383312482853541572780087363938442377933706865252053507077543420534380486492786626556269083255657125025963825610840222568694137138741554679540").unwrap(), B_COEFF);
}

#[test]
fn test_neg_one() {
    let mut o = Fq::one();
    o.negate();

    assert_eq!(NEGATIVE_ONE, o);
}

#[cfg(test)]
use rand::{Rand, SeedableRng, XorShiftRng};

#[test]
fn test_fq_repr_ordering() {
    use std::cmp::Ordering;

    fn assert_equality(a: FqRepr, b: FqRepr) {
        assert_eq!(a, b);
        assert!(a.cmp(&b) == Ordering::Equal);
    }

    fn assert_lt(a: FqRepr, b: FqRepr) {
        assert!(a < b);
        assert!(b > a);
    }

    assert_equality(
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999,
        ]),
    );
    assert_equality(
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9998, 9999, 9999, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9998, 9999, 9999, 9999, 9999,
        ]),
    );
    assert_equality(
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
    );
    assert_lt(
        FqRepr([
            9999, 9999, 9999, 9997, 9999, 9998, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9997, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
    );
    assert_lt(
        FqRepr([
            9999, 9999, 9999, 9997, 9998, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9997, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
    );
    assert_lt(
        FqRepr([
            9, 9999, 9999, 9997, 9998, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
        FqRepr([
            9999, 9999, 9999, 9997, 9999, 9999, 9999, 9999, 9999, 9997, 9999, 9999,
        ]),
    );
}

#[test]
fn test_fq_repr_from() {
    assert_eq!(
        FqRepr::from(100),
        FqRepr([100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    );
}

#[test]
fn test_fq_repr_is_odd() {
    assert!(!FqRepr::from(0).is_odd());
    assert!(FqRepr::from(0).is_even());
    assert!(FqRepr::from(1).is_odd());
    assert!(!FqRepr::from(1).is_even());
    assert!(!FqRepr::from(324834872).is_odd());
    assert!(FqRepr::from(324834872).is_even());
    assert!(FqRepr::from(324834873).is_odd());
    assert!(!FqRepr::from(324834873).is_even());
}

#[test]
fn test_fq_repr_is_zero() {
    assert!(FqRepr::from(0).is_zero());
    assert!(!FqRepr::from(1).is_zero());
    assert!(!FqRepr([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]).is_zero());
}

#[test]
fn test_fq_repr_num_bits() {
    let mut a = FqRepr::from(0);
    assert_eq!(0, a.num_bits());
    a = FqRepr::from(1);
    for i in 1..385 {
        assert_eq!(i, a.num_bits());
        a.mul2();
    }
    assert_eq!(0, a.num_bits());
}

#[test]
fn test_fq_repr_sub_noborrow() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        let mut a = FqRepr::rand(&mut rng);
        a.0[5] >>= 30;
        let mut b = a;
        for _ in 0..10 {
            b.mul2();
        }
        let mut c = b;
        for _ in 0..10 {
            c.mul2();
        }

        assert!(a < b);
        assert!(b < c);

        let mut csub_ba = c;
        csub_ba.sub_noborrow(&b);
        csub_ba.sub_noborrow(&a);

        let mut csub_ab = c;
        csub_ab.sub_noborrow(&a);
        csub_ab.sub_noborrow(&b);

        assert_eq!(csub_ab, csub_ba);
    }

    // Subtracting q+1 from q should produce -1
    let mut qplusone = FqRepr([
        0x5e9063de245e8001,
        0xe39d54522cdd119f,
        0x638810719ac425f0,
        0x685acce9767254a4,
        0xb80f0da5cb537e38,
        0xb117e776f218059d,
        0x99d124d9a15af79d,
        0x7fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]);
    qplusone.sub_noborrow(&FqRepr([
        0x5e9063de245e8002,
        0xe39d54522cdd119f,
        0x638810719ac425f0,
        0x685acce9767254a4,
        0xb80f0da5cb537e38,
        0xb117e776f218059d,
        0x99d124d9a15af79d,
        0x7fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]));
    assert_eq!(
        qplusone,
        FqRepr([
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
        ])
    );
}

#[test]
fn test_fq_repr_add_nocarry() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    // Test for the associativity of addition.
    for _ in 0..1000 {
        let mut a = FqRepr::rand(&mut rng);
        let mut b = FqRepr::rand(&mut rng);
        let mut c = FqRepr::rand(&mut rng);

        // Unset the first few bits, so that overflow won't occur.
        a.0[5] >>= 3;
        b.0[5] >>= 3;
        c.0[5] >>= 3;

        let mut abc = a;
        abc.add_nocarry(&b);
        abc.add_nocarry(&c);

        let mut acb = a;
        acb.add_nocarry(&c);
        acb.add_nocarry(&b);

        let mut bac = b;
        bac.add_nocarry(&a);
        bac.add_nocarry(&c);

        let mut bca = b;
        bca.add_nocarry(&c);
        bca.add_nocarry(&a);

        let mut cab = c;
        cab.add_nocarry(&a);
        cab.add_nocarry(&b);

        let mut cba = c;
        cba.add_nocarry(&b);
        cba.add_nocarry(&a);

        assert_eq!(abc, acb);
        assert_eq!(abc, bac);
        assert_eq!(abc, bca);
        assert_eq!(abc, cab);
        assert_eq!(abc, cba);
    }

    // Adding 1 to (q - 1) should produce zero
    let mut x = FqRepr([
        0xc5e777324a8210bf,
        0x51d0228bd2d9cb18,
        0xcbc42bd0cdafcec2,
        0xef0234cfaee99ea2,
        0xcae87111aa4ae6c8,
        0x930899ec2314e834,
        0x67c4e9228e277244,
        0xae72762315b0e32b,
        0x1e431f2d6f0b3251,
        0xa85518752329c761,
        0x7add306fcee92c18,
        0x1497e8ec9e1ce,
    ]);
    x.add_nocarry(&FqRepr::from(1));
    assert!(x.is_zero());
}

#[test]
fn test_fq_is_valid() {
    let mut a = Fq(MODULUS);
    assert!(!a.is_valid());
    a.0.sub_noborrow(&FqRepr::from(1));
    assert!(a.is_valid());
    assert!(Fq(FqRepr::from(0)).is_valid());

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        let a = Fq::rand(&mut rng);
        assert!(a.is_valid());
    }
}

#[test]
fn test_fq_add_assign() {
    /*
    {
        // Random number
        let mut tmp = Fq(FqRepr([
        ]));
        assert!(tmp.is_valid());
        // Test that adding zero has no effect.
        tmp.add_assign(&Fq(FqRepr::from(0)));
        assert_eq!(
            tmp,
            Fq(FqRepr([
            ]))
        );
        // Add one and test for the result.
        tmp.add_assign(&Fq(FqRepr::from(1)));
        assert_eq!(
            tmp,
            Fq(FqRepr([
            ]))
        );
        // Add another random number that exercises the reduction.
        tmp.add_assign(&Fq(FqRepr([
        ])));
        assert_eq!(
            tmp,
            Fq(FqRepr([
            ]))
        );
        // Add one to (q - 1) and test for the result.
        tmp = Fq(FqRepr([
        ]));
        tmp.add_assign(&Fq(FqRepr::from(1)));
        assert!(tmp.0.is_zero());
        // Add a random number to another one such that the result is q - 1
        tmp = Fq(FqRepr([
        ]));
        tmp.add_assign(&Fq(FqRepr([
        ])));
        assert_eq!(
            tmp,
            Fq(FqRepr([
            ]))
        );
        // Add one to the result and test for it.
        tmp.add_assign(&Fq(FqRepr::from(1)));
        assert!(tmp.0.is_zero());
    }
    */
    // Test associativity

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Generate a, b, c and ensure (a + b) + c == a + (b + c).
        let a = Fq::rand(&mut rng);
        let b = Fq::rand(&mut rng);
        let c = Fq::rand(&mut rng);

        let mut tmp1 = a;
        tmp1.add_assign(&b);
        tmp1.add_assign(&c);

        let mut tmp2 = b;
        tmp2.add_assign(&c);
        tmp2.add_assign(&a);

        assert!(tmp1.is_valid());
        assert!(tmp2.is_valid());
        assert_eq!(tmp1, tmp2);
    }
}

#[test]
fn test_fq_sub_assign() {
    /*
        {
            // Test arbitrary subtraction that tests reduction.
            let mut tmp = Fq(FqRepr([
            ]));
            tmp.sub_assign(&Fq(FqRepr([
            ])));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );

            // Test the opposite subtraction which doesn't test reduction.
            tmp = Fq(FqRepr([
            ]));
            tmp.sub_assign(&Fq(FqRepr([
            ])));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );

            // Test for sensible results with zero
            tmp = Fq(FqRepr::from(0));
            tmp.sub_assign(&Fq(FqRepr::from(0)));
            assert!(tmp.is_zero());

            tmp = Fq(FqRepr([
            ]));
            tmp.sub_assign(&Fq(FqRepr::from(0)));
            assert_eq!(
                tmp,
                Fq(FqRepr([
                ]))
            );
        }
    */
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Ensure that (a - b) + (b - a) = 0.
        let a = Fq::rand(&mut rng);
        let b = Fq::rand(&mut rng);

        let mut tmp1 = a;
        tmp1.sub_assign(&b);

        let mut tmp2 = b;
        tmp2.sub_assign(&a);

        tmp1.add_assign(&tmp2);
        assert!(tmp1.is_zero());
    }
}

#[test]
fn test_fq_mul_assign() {
    let mut tmp = Fq(FqRepr([
        0xbf5fe920d1992880,
        0xe9433a42ccefbff2,
        0xd7f812c1def8c709,
        0xc9186f2f58446f50,
        0xb917d238a7c19af1,
        0xb8d279edb5f43215,
        0x1a004589295e39c7,
        0x53034ee27b5a6dfa,
        0x39e094c7e6e2ac7f,
        0xe52b2e27c5435e57,
        0x5a58f3a8f955e7f,
        0x1463240606093,
    ]));
    tmp.mul_assign(&Fq(FqRepr([
        0x3f5caa8a351082e0,
        0x10e2cbfdb8a93405,
        0xfff3511518ddee13,
        0x81c6b5eae9770cc6,
        0xc5ef81f4273603ef,
        0x11c668d5e825ed48,
        0xc6f28e3f772ce1c5,
        0xbf4aa406ab3a9757,
        0x6984799c3cae5b97,
        0xde4a63b3a95e8ee5,
        0xbf4d903aa33977e1,
        0xd07c25be7743,
    ])));
    assert!(
        tmp == Fq(FqRepr([
            0x4b2cd72171331b9d,
            0x8dde609d06a26f9d,
            0x13204e1c288c8bbe,
            0x368291a479d84648,
            0x1962bb9dabd0c52f,
            0x43af438a16ac1592,
            0x3688aad7d4b9919c,
            0xf031665a127582d7,
            0x42b3219495400fa8,
            0xbb04927b51dd808c,
            0x669d5702378dabcf,
            0x280f8a033a8f,
        ]))
    );

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000000 {
        // Ensure that (a * b) * c = a * (b * c)
        let a = Fq::rand(&mut rng);
        let b = Fq::rand(&mut rng);
        let c = Fq::rand(&mut rng);

        let mut tmp1 = a;
        tmp1.mul_assign(&b);
        tmp1.mul_assign(&c);

        let mut tmp2 = b;
        tmp2.mul_assign(&c);
        tmp2.mul_assign(&a);

        assert_eq!(tmp1, tmp2);
    }

    for _ in 0..1000000 {
        // Ensure that r * (a + b + c) = r*a + r*b + r*c

        let r = Fq::rand(&mut rng);
        let mut a = Fq::rand(&mut rng);
        let mut b = Fq::rand(&mut rng);
        let mut c = Fq::rand(&mut rng);

        let mut tmp1 = a;
        tmp1.add_assign(&b);
        tmp1.add_assign(&c);
        tmp1.mul_assign(&r);

        a.mul_assign(&r);
        b.mul_assign(&r);
        c.mul_assign(&r);

        a.add_assign(&b);
        a.add_assign(&c);

        assert_eq!(tmp1, a);
    }
}

#[test]
fn test_fq_squaring() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000000 {
        // Ensure that (a * a) = a^2
        let a = Fq::rand(&mut rng);

        let mut tmp = a;
        tmp.square();

        let mut tmp2 = a;
        tmp2.mul_assign(&a);

        assert_eq!(tmp, tmp2);
    }
}

#[test]
fn test_fq_inverse() {
    assert!(Fq::zero().inverse().is_none());

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let one = Fq::one();

    for _ in 0..1000 {
        // Ensure that a * a^-1 = 1
        let mut a = Fq::rand(&mut rng);
        let ainv = a.inverse().unwrap();
        a.mul_assign(&ainv);
        assert_eq!(a, one);
    }
}

#[test]
fn test_fq_double() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Ensure doubling a is equivalent to adding a to itself.
        let mut a = Fq::rand(&mut rng);
        let mut b = a;
        b.add_assign(&a);
        a.double();
        assert_eq!(a, b);
    }
}

#[test]
fn test_fq_negate() {
    {
        let mut a = Fq::zero();
        a.negate();

        assert!(a.is_zero());
    }

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Ensure (a - (-a)) = 0.
        let mut a = Fq::rand(&mut rng);
        let mut b = a;
        b.negate();
        a.add_assign(&b);

        assert!(a.is_zero());
    }
}

#[test]
fn test_fq_pow() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for i in 0..1000 {
        // Exponentiate by various small numbers and ensure it consists with repeated
        // multiplication.
        let a = Fq::rand(&mut rng);
        let target = a.pow(&[i]);
        let mut c = Fq::one();
        for _ in 0..i {
            c.mul_assign(&a);
        }
        assert_eq!(c, target);
    }

    for _ in 0..1000 {
        // Exponentiating by the modulus should have no effect in a prime field.
        let a = Fq::rand(&mut rng);

        assert_eq!(a, a.pow(Fq::char()));
    }
}

#[test]
fn test_fq_sqrt() {
    use ff::SqrtField;

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    assert_eq!(Fq::zero().sqrt().unwrap(), Fq::zero());

    for _ in 0..1000 {
        // Ensure sqrt(a^2) = a or -a
        let a = Fq::rand(&mut rng);
        let mut nega = a;
        nega.negate();
        let mut b = a;
        b.square();

        let b = b.sqrt().unwrap();

        assert!(a == b || nega == b);
    }

    for _ in 0..1000 {
        // Ensure sqrt(a)^2 = a for random a
        let a = Fq::rand(&mut rng);

        if let Some(mut tmp) = a.sqrt() {
            tmp.square();

            assert_eq!(a, tmp);
        }
    }
}

#[test]
fn test_fq_from_into_repr() {
    // q + 1 should not be in the field
    assert!(Fq::from_repr(FqRepr([
        0x5e9063de245e8002,
        0xe39d54522cdd119f,
        0x638810719ac425f0,
        0x685acce9767254a4,
        0xb80f0da5cb537e38,
        0xb117e776f218059d,
        0x99d124d9a15af79d,
        0x07fdb925e8a0ed8d,
        0x5eb7e8f96c97d873,
        0xb7f997505b8fafed,
        0x10229022eee2cdad,
        0x1c4c62d92c411,
    ]))
    .is_err());

    // q should not be in the field
    assert!(Fq::from_repr(Fq::char()).is_err());

    // Multiply some arbitrary representations to see if the result is as expected.
    let a = FqRepr([
        0xbf5fe920d1992880,
        0xe9433a42ccefbff2,
        0xd7f812c1def8c709,
        0xc9186f2f58446f50,
        0xb917d238a7c19af1,
        0xb8d279edb5f43215,
        0x1a004589295e39c7,
        0x53034ee27b5a6dfa,
        0x39e094c7e6e2ac7f,
        0xe52b2e27c5435e57,
        0x5a58f3a8f955e7f,
        0x1463240606093,
    ]);
    let mut a_fq = Fq::from_repr(a).unwrap();
    let b = FqRepr([
        0x3f5caa8a351082e0,
        0x10e2cbfdb8a93405,
        0xfff3511518ddee13,
        0x81c6b5eae9770cc6,
        0xc5ef81f4273603ef,
        0x11c668d5e825ed48,
        0xc6f28e3f772ce1c5,
        0xbf4aa406ab3a9757,
        0x6984799c3cae5b97,
        0xde4a63b3a95e8ee5,
        0xbf4d903aa33977e1,
        0xd07c25be7743,
    ]);
    let b_fq = Fq::from_repr(b).unwrap();
    let c = FqRepr([
        0x4b2cd72171331b9d,
        0x8dde609d06a26f9d,
        0x13204e1c288c8bbe,
        0x368291a479d84648,
        0x1962bb9dabd0c52f,
        0x43af438a16ac1592,
        0x3688aad7d4b9919c,
        0xf031665a127582d7,
        0x42b3219495400fa8,
        0xbb04927b51dd808c,
        0x669d5702378dabcf,
        0x280f8a033a8f,
    ]);
    a_fq.mul_assign(&b_fq);
    assert_eq!(a_fq.into_repr(), c);

    // Zero should be in the field.
    assert!(Fq::from_repr(FqRepr::from(0)).unwrap().is_zero());

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // Try to turn Fq elements into representations and back again, and compare.
        let a = Fq::rand(&mut rng);
        let a_repr = a.into_repr();
        let b_repr = FqRepr::from(a);
        assert_eq!(a_repr, b_repr);
        let a_again = Fq::from_repr(a_repr).unwrap();

        assert_eq!(a, a_again);
    }
}

#[test]
fn test_fq_num_bits() {
    assert_eq!(Fq::NUM_BITS, 753);
    assert_eq!(Fq::CAPACITY, 752);
}

#[test]
fn fq_field_tests() {
    ::tests::field::random_field_tests::<Fq>();
    ::tests::field::random_sqrt_tests::<Fq>();
    ::tests::field::random_frobenius_tests::<Fq, _>(Fq::char(), 13);
    ::tests::field::from_str_tests::<Fq>();
}

#[test]
fn test_fq_ordering() {
    // FqRepr's ordering is well-tested, but we still need to make sure the Fq
    // elements aren't being compared in Montgomery form.
    for i in 0..100 {
        assert!(
            Fq::from_repr(FqRepr::from(i + 1)).unwrap() > Fq::from_repr(FqRepr::from(i)).unwrap()
        );
    }
}

#[test]
fn fq_repr_tests() {
    ::tests::repr::random_repr_tests::<FqRepr>();
}

#[test]
fn test_fq_legendre() {
    use ff::LegendreSymbol::*;
    use ff::SqrtField;

    assert_eq!(QuadraticResidue, Fq::one().legendre());
    assert_eq!(Zero, Fq::zero().legendre());

    assert_eq!(
        QuadraticNonResidue,
        Fq::from_repr(FqRepr::from(2)).unwrap().legendre()
    );
    assert_eq!(
        QuadraticResidue,
        Fq::from_repr(FqRepr::from(4)).unwrap().legendre()
    );
}

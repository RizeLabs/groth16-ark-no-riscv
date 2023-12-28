
// use ark_ff::QuadExtField;
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_groth16::data_structures;
// For randomness (during paramgen and proof generation)
use ark_std::rand::{Rng, RngCore, SeedableRng};

// Bring in some tools for using pairing-friendly curves
// We're going to use the BLS12-377 pairing-friendly elliptic curve.
use ark_bls12_377::{Bls12_377, Fr, Config, FqConfig};
use ark_ff::{Field, BigInteger, PrimeField, Fp, MontBackend};
use ark_std::test_rng;
use ark_ec::{pairing::{Pairing, PairingOutput}, short_weierstrass::Affine, models::*};
use ark_bn254::Bn254;
use std::fs::File;


use ark_groth16::data_structures::*;
use ark_ec::{models::bls12::Bls12, AffineRepr};

use serde_json;

// We'll use these interfaces to construct our circuit.
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};

use std::str::FromStr;
// use std::fs::File;
use std::io::Write;



use serde::{Serialize, Deserialize, de};
#[derive(Serialize, Deserialize, Debug)]
struct Test{
    i: i32,
    f: f64
}



const MIMC_ROUNDS: usize = 1;


fn mimc<F: Field>(mut xl: F, mut xr: F, constants: &[F]) -> F {
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for i in 0..MIMC_ROUNDS {
        let mut tmp1 = xl;
        tmp1.add_assign(&constants[i]);
        let mut tmp2 = tmp1;
        tmp2.square_in_place();
        tmp2.mul_assign(&tmp1);
        tmp2.add_assign(&xr);
        xr = xl;
        xl = tmp2;
    }

    xl
}

struct AddDemo<F: Field> {
    x: Option<F>,
    y: Option<F>,
}

impl< F: Field> ConstraintSynthesizer<F> for AddDemo<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        

        let a = cs.new_witness_variable(|| self.x.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.y.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut a = self.x.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.y.ok_or(SynthesisError::AssignmentMissing)?;

            a.mul_assign(&b);
            Ok(a)
        })?;
        cs.enforce_constraint(
            lc!() + a, 
            lc!() + b,  
            lc!() + c
        )?;

        Ok(())
    }
}



/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
struct MiMCDemo<'a, F: Field> {
    xl: Option<F>,
    xr: Option<F>,
    constants: &'a [F],
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, F: Field> ConstraintSynthesizer<F> for MiMCDemo<'a, F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        // Allocate the first component of the preimage.
        let mut xl_value = self.xl;
        let mut xl =
            cs.new_witness_variable(|| xl_value.ok_or(SynthesisError::AssignmentMissing))?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.xr;
        let mut xr =
            cs.new_witness_variable(|| xr_value.ok_or(SynthesisError::AssignmentMissing))?;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let ns = ns!(cs, "round");
            let cs = ns.cs();

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.square_in_place();
                e
            });
            let tmp =
                cs.new_witness_variable(|| tmp_value.ok_or(SynthesisError::AssignmentMissing))?;

            cs.enforce_constraint(
                lc!() + xl + (self.constants[i], Variable::One),
                lc!() + xl + (self.constants[i], Variable::One),
                lc!() + tmp,
            )?;

            // new_xL = xR + (xL + Ci)^3
            // new_xL = xR + tmp * (xL + Ci)
            // new_xL - xR = tmp * (xL + Ci)
            let new_xl_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.mul_assign(&tmp_value.unwrap());
                e.add_assign(&xr_value.unwrap());
                e
            });

            let new_xl = if i == (MIMC_ROUNDS - 1) {
                // This is the last round, xL is our image and so
                // we allocate a public input.
                cs.new_input_variable(|| new_xl_value.ok_or(SynthesisError::AssignmentMissing))?
            } else {
                cs.new_witness_variable(|| new_xl_value.ok_or(SynthesisError::AssignmentMissing))?
            };

            cs.enforce_constraint(
                lc!() + tmp,
                lc!() + xl + (self.constants[i], Variable::One),
                lc!() + new_xl - xr,
            )?;

            // xR = xL
            xr = xl;
            xr_value = xl_value;

            // xL = new_xL
            xl = new_xl;
            xl_value = new_xl_value;
        }

        Ok(())
    }
}

// struct AddDemo<'a, F: Field> {
//     x: Option<F>,
//     y: Option<F>,
// }



pub fn main() {
    // TODO: Implement your guest code here

    // read the input

     // We're going to use the Groth16 proving system.
     use ark_groth16::Groth16;
     use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
     

     // This may not be cryptographically safe, use
     // `OsRng` (for example) in production software.
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    let m: Test = serde_json::from_str(r#"{"i":1,"f":321.456}"#).unwrap();

    // let pk: ProvingKey<Bls12<Config>> = ProvingKey{
    //     vk: VerifyingKey{
    //         alpha_g1: ("157688269239423920488757034575563957992998721480997560727259196765054466375304217563455209429723928799786509789204", "92494351756799635743545654203445151139568786820666293670690042234069110323545462094917081724047634571459647378785"),
    //         beta_g2: (QuadExtField(40309996799874016708304063195445742266857014087233984337505307782499823223356411564421071414488365236732903748261 + 51139483055188025264239567818697237602206494234929828899025269799259997293569890812225431839299696146767117281215 * u), QuadExtField(215741730292968840427880441845958534902475716374859383658700160497431888863692339148841005303554482593751534875886 + 117727143339335713836759796386770298235354970797888184286303747211431290495937278208525610226703111736070094327541 * u)),
    //         gamma_g2: (QuadExtField(35753944434878852917227197931156179070540366520356443533127173872106177388975908318716916027010741667639927009325 + 41603867110274746990520819231757733680285830513968789310514197412520562766519829901526080371854174129816172208795 * u), QuadExtField(51161818228906916424278730673149095725928662245915239351050067830144778209616797974237597454384064549676746671804 + 111034061069987665078959018085841376978343200928201031863242369541311189640296209669521903745633318137853452751041 * u)),
    //         delta_g2: (QuadExtField(34257440215510559692116486933800250287868872144323562592557759888730320341049728144082616316100079048960150637668 + 63364451824478687290741554314414352910655081853273562553416931405643710499609224109573145623197014382740644007427 * u), QuadExtField(233645475720759641296723869951257593841119967404191756521816508350176696394656125991839606921420544739570854425273 + 39821734696151894117208007032675951674773480312741128076937903822342089266965272060558354356777683143050368255440 * u))
    //     }
    // }
    // ProvingKey { vk: VerifyingKey { alpha_g1: (157688269239426336445182447868729074155431441435293920488757034575563957992998721480997560727259196765054466375304217563455209429723928799786509789204, 92494351756799635743545654203445151139568786820666293670690042234069110323545462094917081724047634571459647378785), beta_g2: (QuadExtField(40309996799874016708304063195445742266857014087233984337505307782499823223356411564421071414488365236732903748261 + 51139483055188025264239567818697237602206494234929828899025269799259997293569890812225431839299696146767117281215 * u), QuadExtField(215741730292968840427880441845958534902475716374859383658700160497431888863692339148841005303554482593751534875886 + 117727143339335713836759796386770298235354970797888184286303747211431290495937278208525610226703111736070094327541 * u)), gamma_g2: (QuadExtField(35753944434878852917227197931156179070540366520356443533127173872106177388975908318716916027010741667639927009325 + 41603867110274746990520819231757733680285830513968789310514197412520562766519829901526080371854174129816172208795 * u), QuadExtField(51161818228906916424278730673149095725928662245915239351050067830144778209616797974237597454384064549676746671804 + 111034061069987665078959018085841376978343200928201031863242369541311189640296209669521903745633318137853452751041 * u)), delta_g2: (QuadExtField(34257440215510559692116486933800250287868872144323562592557759888730320341049728144082616316100079048960150637668 + 10655081853273562553416931405643710499609224109573145623197014382740644007427 * u), QuadExtField(233645475720759641296723869951257593841119967404191756521816508350176696394656125991839606921420544739570854425273 + 39821734696151894117208007032675951674773480312741128076937903822342089266965272060558354356777683143050368255440 * u)), gamma_abc_g1: [(28454713963302267733229343191213169744887422571642017288140930985892588269484581977316394234592442098846389942651, 97600623346627390842649724339475076599406582219409802747101284077587196888537760577216895477598716546446165344169), (10350613430705019622276493248089987121722587197342105245129000306465464106329037376879457228886447215346510344679, 236467999362788681687557360553050217455575251754273799864216711372095718748173565969368610929910302815036571309160)] }, beta_g1: (43644129049407033424146439623914696916611744176451523519118514320337902746267426569155713029729769094227646761356, 49153804898081092162164457631298348098483507158099548758568523857465127236122782847788157916373910793144360759990), delta_g1: (191935433628351209870906206310330994017468828384833245066888688920930201866077647725968473129912952173743070764737, 196447471145545993374897995541998722420883231827042589206730287908808689356387669338124457129336618100930980527344), a_query: [(85043122881332773252480015362894623592295962400987352258371619170775345832582668365777946826746046001394115304144, 63965065477867374526873480751160516891209868306337695203872003760695518714337124250166294747607336857932055405140), (254073118820571406345848453516395632713553303731049050763535096359832532204188950172261280173104348932354125207453, 49770621573012551617262648815369837582599710610782434028834466588607684450025793672548381482433817217668065478222), (172276506593819653213084177879340512764004144442060567885573700647466120653971306102945162915893367820039932577474, 201186211884756448154683397502952138379729557969727607643098801210755384486342848253553147916765455665782085148599), infinity], b_g1_query: [infinity, infinity, infinity, (172276506593819653213084177879340512764004144442060567885573700647466120653971306102945162915893367820039932577474, 201186211884756448154683397502952138379729557969727607643098801210755384486342848253553147916765455665782085148599)], b_g2_query: [infinity, infinity, infinity, (QuadExtField(219003397245807300332276748957042619263220224525578168940687870749776445123399370753265130770995972191533043574097 + 164791715471177607017292008850992904253038403062792258308542870384834102146273050107235135760415919286846435398531 * u), QuadExtField(224380971462997074636579005210705881233773543107600858414486345334047122917202598794307216806737761833978166924817 + 110299508448747270267732618712735941980152949391059333297644900120602967966873810307385458767039782453002581016053 * u))], h_query: [(167669157375163289147467932763423184461584185052566785682468306311202554376030146486674781151826375727703670125671, 25341783463293744813031685742165598801468661104028887864278833523634278805982522425614849910119655014204326098133), (85933066238111777532628343629003021920006573295287621670514171906814466553298856971790454844394440293405450919486, 217116334592621575542441369498752503292106502227426842613677394317955598335598780074992763235091892088261495975610), (253920070553105904349769367884462868645871222740089320341265199002617389414013305218707990185129096129161318400874, 175229756395220963502421229778693179994914301728554570256258371334809873428572646200753260819163014503644634267056)], l_query: [(85432010713061356380527841941196315771123272262751600108969639014879760964012892903716942363195646422440865039721, 227759217758362965220852747817348959978885214924064368620946168096888442275417710787397669216391788565797873703112), (213754530845422009880061899823456739427620066022581605135788322559703564232510056906244691297959605307445904306437, 225681801842611922370662154031306791854931509861146980640929968274194883024810478126201066560834998207770440467140)] };

 
     let (pk, vk) = {
       
        let c = AddDemo::<Fr> {
            x: None,
            y: None,
        };
 
         Groth16::<Bls12_377>::setup(c, &mut rng).unwrap()
     };


    println!("pk: {:?}", pk);
    println!("vk: {:?}", vk);

     
 
    //  // Prepare the verification key (for proof verification)
     let pvk = Groth16::<Bls12_377>::process_vk(&vk).unwrap();

    //  println!("pvk: {:?}", pvk);
 
 
    // //  // Let's benchmark stuff!
     const SAMPLES: u32 = 1;
   
 
     for _ in 0..SAMPLES {
    //      // Generate a random preimage and compute the image
            let x = Fr::from(4);
            let y = Fr::from(5);
            let z = Fr::from(20);

       
            {
                
            let c = AddDemo {
                x: Some(x),
                y: Some(y),
            };

                // Create a groth16 proof with our parameters.
                let proof = Groth16::<Bls12_377>::prove(&pk, c, &mut rng).unwrap();
                // println!("proof: {:?}", proof);
                
                // println!("proof.a: {:?}", );

                let string_proof = proof_to_proof_str(&proof);

                // println!("string_proof: {:?}", string_proof);
                let mut bytes: Vec<u8> = vec![];

                let mut compressed_bytes = Vec::new();
                proof.serialize_compressed(&mut compressed_bytes).unwrap();

                // println!("compressed_bytes: {:?}", compressed_bytes);

                // let mut file = File::create("data.bin").expect("Failed to create file");
                // file.write_all(&compressed_bytes).expect("Failed to write to file");

                // let mut file_read = File::open("data.bin").expect("Failed to open file");

                // Read the contents of the file into a Vec<u8>
                let buffer = match std::fs::read("data.bin") {
                    Ok(contents) => contents,
                    Err(e) => {
                        eprintln!("Error reading file: {}", e);
                        return;
                    }
                };

                println!("buffer: {:?}", buffer);
                // let a_compressed = G1Affine::deserialize_compressed(&*compressed_bytes).unwrap();

                let proof_back = Proof::<Bls12_377>::deserialize_compressed(&*buffer).unwrap();
                println!("proof_back: {:?}", proof_back);


                let proof_json = serde_json::to_string(&string_proof).unwrap();

                // println!("proof_json: {:?}", proof_json);

                let proof_derived_string: ProofStr = serde_json::from_str(&proof_json).unwrap();

                // println!("proof_derived_string: {:?}", proof_derived_string);

                // let proof_derived: Proof::<Bls12<Config>> = Proof{
                //     a: E::G1Affine::new(
                //         E::BaseField::from_str(&a_x)?,
                //         E::BaseField::from_str(&a_y)?,
                //         false,
                //     )
                // }
                

            


                assert!(
                    Groth16::<Bls12_377>::verify_with_processed_vk(&pvk, &[z], &proof).unwrap()
                );
                
            }

 
     }
    


    // write public output to the journal
}


fn proof_to_proof_str(proof: &Proof<Bls12<Config>>) -> ProofStr {
    let a_xy: Affine<ark_bls12_377::g1::Config> = proof.a;
    let a_x: ark_ff::Fp<ark_ff::MontBackend<ark_bls12_377::FqConfig, 6>, 6> = a_xy.x;
    let b_xy: Affine<ark_bls12_377::g2::Config> = proof.b;
    let c_xy: Affine<ark_bls12_377::g1::Config> = proof.c;

    let b_c0_c0 = b_xy.x.c0.to_string();
    let b_c0_c1 = b_xy.y.c1.to_string();
    let b_c1_c0 = b_xy.x.c0.to_string();
    let b_c1_c1 = b_xy.y.c1.to_string();

    ProofStr {
        a: (a_xy.x.to_string(), a_xy.y.to_string()),
        b: ((b_c0_c0, b_c0_c1), (b_c1_c0, b_c1_c1)),
        c: (c_xy.x.to_string(), c_xy.y.to_string()),
    }
}

#[derive(Serialize, Deserialize, Debug)]
struct ProofStr {
    a: (String, String),
    b: ((String, String), (String, String)), // Represent each QuadExtField by two BaseFields
    c: (String, String),
}

// fn parse_proof<E: Pairing>(proof_string: &ProofStr) -> Result<Proof<E>, Box<dyn std::error::Error>> 
// where

// {
    
//     let a: Affine<ark_bls12_377::g1::Config> = Affine {
//         x: <E::G1Affine as Into<E::G1Prepared>>::into(proof.a),
//         y: *ark_bls12_377::g1::G1Affine::y(&proof_string.a.1)?,
//         infinity: false,
//     };

//     Ok(Proof::default())
// }
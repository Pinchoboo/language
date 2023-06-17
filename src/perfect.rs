use std::{
    collections::{HashMap, HashSet},
    fs::File,
    io::BufReader,
};

use crate::{parser::PerfectMap, typecheck::ConstValue};

pub fn find_hash_function(p: &mut PerfectMap) {
    let vals = &p.values;
    p.args = if let Some(args) = get_perfect(vals) {
        args
    } else {
        let mut args = vec![0];
        while !is_perfect(vals, &args) {
            for i in 0..(args.len()) {
                if args[i] == 63 {
                    if i == 2 {
                        print!(".");
                    }
                    args[i] = 0;
                    if i == args.len() - 1 {
                        args.push(0);
                        break;
                    }
                } else {
                    args[i] += 1;
                    break;
                }
            }
        }
        _ = store_perfect(vals, &args);
        args
    };
    println!("\nfound perfect hashing algorithm for {}", p.identifier);
    print!("idx = (0");
    for i in p.args.iter().rev() {
        print!("^(x>>{i})")
    }
    println!(")%{}", p.entries.len());
}

fn is_perfect(vals: &Vec<(ConstValue, ConstValue)>, args: &Vec<u32>) -> bool {
    let r: HashSet<u64> = vals
        .iter()
        .map(|v| {
            let mut r = 0;
            for a in args {
                match v.0 {
                    crate::typecheck::ConstValue::Bits(v) => r ^= v.rotate_right(*a),
                    crate::typecheck::ConstValue::Map(_) => todo!(),
                }
            }
            r % (vals.len() as u64)
        })
        .collect();
    //println!("{args:?} -> {r:?}");
    r.len() == vals.len()
}

pub fn get_order(vals: &Vec<(ConstValue, ConstValue)>, args: &Vec<u32>) -> Vec<u64> {
    vals.iter()
        .map(|v| {
            let mut r = 0;
            for a in args {
                match v.0 {
                    crate::typecheck::ConstValue::Bits(v) => r ^= v.rotate_right(*a),
                    crate::typecheck::ConstValue::Map(_) => todo!(),
                }
            }
            r % (vals.len() as u64)
        })
        .collect()
}

fn get_perfect(vals: &Vec<(ConstValue, ConstValue)>) -> Option<Vec<u32>> {
    let file = File::open("./cache/perfect").ok()?;
    let r: HashMap<String, Vec<u32>> = serde_json::from_reader(BufReader::new(file)).ok()?;
    let r: HashMap<Vec<u64>, Vec<u32>> = r.into_iter().fold(HashMap::new(), |mut m, (k, v)| {
        m.insert(serde_json::from_str(&k).unwrap(), v);
        m
    });
    r.get(&{
        let mut set = vals
            .iter()
            .map(|(k, _)| match k {
                ConstValue::Bits(b) => *b,
                ConstValue::Map(_) => todo!(),
            })
            .collect::<Vec<_>>();
        set.sort();
        set
    })
    .cloned()
}

fn store_perfect(vals: &Vec<(ConstValue, ConstValue)>, args: &Vec<u32>) -> Result<(), ()> {
    let mut r: HashMap<Vec<u64>, Vec<u32>> = if let Ok(f) = File::open("./cache/perfect") {
        serde_json::from_reader(BufReader::new(f))
            .map(|r: HashMap<String, Vec<u32>>| {
                r.into_iter().fold(HashMap::new(), |mut m, (k, v)| {
                    m.insert(serde_json::from_str(&k).unwrap(), v);
                    m
                })
            })
            .unwrap_or(HashMap::new())
    } else {
        HashMap::new()
    };
    r.insert(
        {
            let mut set = vals
                .iter()
                .map(|(k, _)| match k {
                    ConstValue::Bits(b) => *b,
                    ConstValue::Map(_) => todo!(),
                })
                .collect::<Vec<_>>();
            set.sort();
            set
        },
        args.clone(),
    );
    let r: HashMap<String, Vec<u32>> = r
        .iter()
        .map(|(k, v)| (serde_json::to_string(k).unwrap(), v))
        .fold(HashMap::new(), |mut m, (k, v)| {
            m.insert(k, v.clone());
            m
        });
    std::fs::write("./cache/perfect", serde_json::to_string_pretty(&r).unwrap()).map_err(|_| ())?;
    Ok(())
}

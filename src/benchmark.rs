
#[cfg(test)]
mod tests {
    /*global_asm!(include_str!("../benchmark/link/fill.asm"));
	extern "C" {
		fn hashSetFill(size: u64) -> u64;
		fn hashSetFloatFill(size: u64) -> u64;
	}*/
    use std::{
        collections::{HashMap, HashSet},
        fs::File,
        time::Instant, arch::global_asm,
    };

    use inkwell::context::Context;
    use prettytable::{row, table};

    use crate::{check, compile, parser};
    fn average(t: u64, f: impl Fn() -> f64) -> f64 {
        (0..t).map(|_| f()).sum::<f64>() / (t as f64)
    }

    #[test]
    fn fill() -> Result<(), ()> {
        let fp = parser::FileParser::new("./benchmark/fill.mpl").unwrap();
        let mut ast = fp.parse().unwrap();
        check(&mut ast);
        let context = Context::create();
        let builder = &context.create_builder();
        let module = &context.create_module("module");
        let compiler = compile::compile(&context, builder, module, ast);

        let set_fill = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("hashSetFill");
        let drop_set = compiler.get_function::<unsafe extern "C" fn(u64) -> ()>("dropHashSet");

        let mplset = |size| unsafe {
            let now = Instant::now();
            let set = set_fill(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop_set(set);
            time
        };

        let set_fill =
            compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("hashSetFloatFill");
        let drop_set = compiler.get_function::<unsafe extern "C" fn(u64) -> ()>("dropHashSetFloat");

        let mplsetfloat = |size| unsafe {
            let now = Instant::now();
            let set = set_fill(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop_set(set);
            time
        };

        let map_fill = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("hashMapFill");
        let map_free = compiler.get_function::<unsafe extern "C" fn(u64) -> ()>("dropHashMap");
        let mplmap = |size| unsafe {
            let now = Instant::now();
            let set = map_fill(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            map_free(set);
            time
        };

        let rustset = |size| {
            let now = Instant::now();
            let mut m: HashSet<u64> = HashSet::new();
            for i in 0..size {
                m.insert(i);
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop(m);
            time
        };
        let rustmap = |size| {
            let now = Instant::now();
            let mut m: HashMap<u64, u64> = HashMap::new();
            for _ in 0..size {
                m.insert(m.len() as u64, m.len() as u64);
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop(m);
            time
        };
        let mut t = table!([H5c->"Fill Benchmark"],[
            "Keys",
            "MPL set",
            "MPL map",
            "MPL set float",
            "Rust set",
            "Rust map"
        ]);
        for p in 2..5 {
            let n = 10u64.pow(p);
            let runs = 1;
            t.add_row(row![
                //format!("{runs}"),
                format!("10^{p}"),
                format!("{:.2}ms", average(runs, || { mplset(n) })),
                //format!("{:.2}ms", average(runs, || { mplmap(n) })),
                //format!("{:.2}ms", average(runs, || { mplsetfloat(n) })),
                //format!("{:.2}ms", average(runs, || { rustset(n) })),
                //format!("{:.2}ms", average(runs, || { rustmap(n) }))
            ]);
        }
        t.printstd();
        let mut f = File::create("./benchmark/fill.txt").unwrap();
        _ = t.print(&mut f);
        Ok(())
    }

    //#[test]
    fn lookup() -> Result<(), ()> {
        let fp = parser::FileParser::new("./benchmark/lookup.mpl").unwrap();
        let mut ast = fp.parse().unwrap();
        check(&mut ast);
        let context = Context::create();
        let builder = &context.create_builder();
        let module = &context.create_module("module");

        let compiler = compile::compile(&context, builder, module, ast);

        let map_fill_half =
            compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("hashMapFillHalf");
        let map_lookup =
            compiler.get_function::<unsafe extern "C" fn(u64, u64) -> u64>("hashMapLookup");
        let drop_map = compiler.get_function::<unsafe extern "C" fn(u64) -> ()>("dropHashMap");

        let mplmap = |size| unsafe {
            let map = map_fill_half(size);
            let now = Instant::now();
            std::hint::black_box(map_lookup(map, size));
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop_map(map);
            time
        };
        let rustmap = |size| {
            let mut map: HashMap<u64, u64> = HashMap::new();
            for i in (0..size).step_by(2) {
                map.insert(i, i);
            }
            let now = Instant::now();
            let mut r = 0;
            for i in 0..size {
                if let Some(v) = map.get(&i) {
                    r += std::hint::black_box(*v);
                }
            }
            _ = std::hint::black_box(r);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop(map);
            time
        };
        let mut t = table!([H3c->"Lookup Benchmark 50% Hit"],[
            "Keys",
            "MPL map",
            "RUST map",
        ]);
        for p in 2..6 {
            let n = 10u64.pow(p);
            let runs = 1; //4u64.pow(8 - p);
            t.add_row(row![
                //format!("{runs}"),
                format!("10^{p}"),
                format!("{:.2}ms", average(runs, || { mplmap(n) })),
                format!("{:.2}ms", average(runs, || { rustmap(n) })),
            ]);
        }
        t.printstd();
        let mut f = File::create("./benchmark/lookup.txt").unwrap();
        _ = t.print(&mut f);
        Ok(())
    }
}

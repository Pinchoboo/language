#[cfg(test)]
mod tests {
    use crate::{check, compile, parser};
    use get_size::GetSize;
    use get_size_derive::GetSize;
    use inkwell::context::Context;
    use prettytable::{row, table, Table};
    use std::{
        collections::{HashMap, HashSet, LinkedList, VecDeque},
        fmt::Debug,
        fs::File,
        mem::take,
        time::Instant,
    };
    use std::{fmt::Display, fs::OpenOptions, io::Write, ops::AddAssign};

    const RUNS: u32 = {
        #[cfg(feature = "heapsize")]
        {
            1
        }
        #[cfg(not(feature = "heapsize"))]
        {
            8
        }
    };

    fn average(t: u32, mut f: impl FnMut() -> f64) -> f64 {
        (0..t).map(|_| f()).sum::<f64>() / (t as f64)
    }
    fn sum2<A: AddAssign<A> + Default, B: AddAssign<B> + Default>(
        t: u32,
        f: impl Fn() -> (A, B),
    ) -> (A, B) {
        (0..t).fold((A::default(), B::default()), |mut acc, _| {
            let f = f();
            acc.0 += f.0;
            acc.1 += f.1;
            acc
        })
    }

    fn sum3<A: AddAssign<A> + Default, B: AddAssign<B> + Default, C: AddAssign<C> + Default>(
        t: u32,
        f: impl Fn() -> (A, B, C),
    ) -> (A, B, C) {
        (0..t).fold((A::default(), B::default(), C::default()), |mut acc, _| {
            let f = f();
            acc.0 += f.0;
            acc.1 += f.1;
            acc.2 += f.2;
            acc
        })
    }

    fn table_to_latex_tabular_inner(t: Table) -> String {
        let mut s = String::new();
        for r in &t {
            for (p, c) in r.iter().enumerate() {
                if p != 0 {
                    s.push('&')
                }
                s.push_str(c.get_content().as_str());
            }
            s.push_str("\\\\ \\hline\n");
        }
        s
    }

    #[test]
    fn benchmark() -> Result<(), ()> {
        fill()?;
        lookup()?;
        pushpop()?;
        tree()?;
        //graph()?;
        //heap()?;
        Ok(())
    }

    fn fill() -> Result<(), ()> {
        let fp = parser::FileParser::new("./benchmark/fill.mpl").unwrap();
        let mut ast = fp.parse().unwrap();
        check(&mut ast);
        let context = Context::create();
        let builder = &context.create_builder();
        let module = &context.create_module("module");
        let compiler = compile::compile(&context, builder, module, ast);

        let heap_size = compiler.get_function::<unsafe extern "C" fn() -> u64>("heapSize");
        let set_fill = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("hashSetFill");
        let drop_set = compiler.get_function::<unsafe extern "C" fn(u64) -> ()>("dropHashSet");

        let mplset = |size| unsafe {
            let initialsize = heap_size();
            let now = Instant::now();
            let set = set_fill(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let finalsize = heap_size();
            drop_set(set);
            assert!(heap_size() == initialsize);
            (time, finalsize)
        };

        let set_fill =
            compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("hashSetFloatFill");
        let drop_set = compiler.get_function::<unsafe extern "C" fn(u64) -> ()>("dropHashSetFloat");

        let mplsetfloat = |size| unsafe {
            let initialsize = heap_size();
            let now = Instant::now();
            let set = set_fill(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let finalsize = heap_size();
            drop_set(set);
            assert!(heap_size() == initialsize);
            (time, finalsize)
        };

        let map_fill = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("hashMapFill");
        let drop_map = compiler.get_function::<unsafe extern "C" fn(u64) -> ()>("dropHashMap");
        let mplmap = |size| unsafe {
            let initialsize = heap_size();
            let now = Instant::now();
            let map = map_fill(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let finalsize = heap_size();
            drop_map(map);
            assert!(heap_size() == initialsize);
            (time, finalsize)
        };
        let rustvec = |size| {
            let now = Instant::now();
            let mut m: Vec<u64> = Vec::with_capacity(0);
            for i in 0..size {
                m.push(std::hint::black_box(i * i));
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let space = m.get_size() as u64;
            drop(m);
            (time, space)
        };

        let rustset = |size| {
            let now = Instant::now();
            let mut m: HashSet<u64> = HashSet::new();
            for i in 0..size {
                m.insert(i * 7);
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let space = m.get_size() as u64;
            drop(m);
            (time, space)
        };
        let rustmap = |size| {
            let now = Instant::now();
            let mut m: HashMap<u64, u64> = HashMap::new();
            for _ in 0..size {
                m.insert((m.len() * 7) as u64, m.len() as u64);
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let space = m.get_size() as u64;
            drop(m);
            (time, space)
        };
        let mut t = if cfg!(feature = "heapsize") {
            table!([H7c->"Benchmark Space"],[
                "Keys",
                "MPL set",
                "MPL map",
                "MPL set float",
                "Rust vec",
                "Rust set",
                "Rust map"
            ])
        } else {
            table!([H7c->"Fill Benchmark"],[
                "Keys",
                "MPL set",
                "MPL map",
                "MPL set float",
                "Rust vec",
                "Rust set",
                "Rust map"
            ])
        };
        for p in 2..9 {
            let n = 10u64.pow(p);
            let (mplsettime, mplsetspace) = sum2(RUNS, || mplset(n));
            let (mplsetfloattime, mplsetfloatspace) = sum2(RUNS, || mplsetfloat(n));
            let (mplmaptime, mplmapspace) = sum2(RUNS, || mplmap(n));
            let (rustvectime, rustvecspace) = sum2(RUNS, || rustvec(n));
            let (rustsettime, rustsetspace) = sum2(RUNS, || rustset(n));
            let (rustmaptime, rustmapspace) = sum2(RUNS, || rustmap(n));
            #[cfg(not(feature = "heapsize"))]
            t.add_row(row![
                //format!("{runs}"),
                format!("10^{p}"),
                format!("{:.2}ms", mplsettime / RUNS as f64),
                format!("{:.2}ms", mplmaptime / RUNS as f64),
                format!("{:.2}ms", mplsetfloattime / RUNS as f64),
                format!("{:.2}ms", rustvectime / RUNS as f64),
                format!("{:.2}ms", rustsettime / RUNS as f64),
                format!("{:.2}ms", rustmaptime / RUNS as f64)
            ]);
            #[cfg(feature = "heapsize")]
            t.add_row(row![
                //format!("{runs}"),
                format!("10^{p}"),
                format!("{:.2} B", mplsetspace / RUNS as u64),
                format!("{:.2} B", mplmapspace / RUNS as u64),
                format!("{:.2} B", mplsetfloatspace / RUNS as u64),
                format!("{:.2} B", rustvecspace / RUNS as u64),
                format!("{:.2} B", rustsetspace / RUNS as u64),
                format!("{:.2} B", rustmapspace / RUNS as u64)
            ]);
        }
        #[cfg(feature = "heapsize")]
        let path = "./benchmark/fill_space.txt";
        #[cfg(not(feature = "heapsize"))]
        let path = "./benchmark/fill.txt";
        t.printstd();
        let mut f = File::create(path).unwrap();
        _ = t.print(&mut f);
        f = OpenOptions::new()
            .write(true)
            .append(true)
            .open(path)
            .unwrap();
        _ = writeln!(f, "{}", table_to_latex_tabular_inner(t));
        Ok(())
    }

    fn lookup() -> Result<(), ()> {
        #[cfg(feature = "heapsize")]
        return Ok(());
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
            map_lookup(map, size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop_map(map);
            time
        };
        let rustmap = |size| {
            let mut map: HashMap<u64, u64> = HashMap::new();
            for i in (0..size).step_by(2) {
                std::hint::black_box(map.insert(i * 7, i));
            }
            let now = Instant::now();
            let mut r = 0;
            for i in 0..size {
                if let Some(v) = map.get(&(i * 7)) {
                    r += std::hint::black_box(*v);
                }
            }
            std::hint::black_box(r);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop(map);
            time
        };
        let mut t = table!([H3c->"Lookup Benchmark 50% Hit"],[
            "Keys",
            "MPL map",
            "Rust map",
        ]);
        for p in 2..8 {
            let n = 10u64.pow(p);
            t.add_row(row![
                //format!("{runs}"),
                format!("10^{p}"),
                format!("{:.2}ms", average(RUNS, || { mplmap(n) })),
                format!("{:.2}ms", average(RUNS, || { rustmap(n) })),
            ]);
        }
        t.printstd();
        let mut f = File::create("./benchmark/lookup.txt").unwrap();
        _ = t.print(&mut f);
        f = OpenOptions::new()
            .write(true)
            .append(true)
            .open("./benchmark/lookup.txt")
            .unwrap();
        _ = writeln!(f, "{}", table_to_latex_tabular_inner(t));
        Ok(())
    }

    fn pushpop() -> Result<(), ()> {
        let fp = parser::FileParser::new("./benchmark/pushpop.mpl").unwrap();
        let mut ast = fp.parse().unwrap();
        check(&mut ast);
        let context = Context::create();
        let builder = &context.create_builder();
        let module = &context.create_module("module");
        let compiler = compile::compile(&context, builder, module, ast);

        let heap_size = compiler.get_function::<unsafe extern "C" fn() -> u64>("heapSize");

        let pushstack = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("stackInsertN");
        let popstack = compiler.get_function::<unsafe extern "C" fn(u64, u64) -> ()>("stackTakeN");

        let mplstack = |size| unsafe {
            let space1 = heap_size();
            let now = Instant::now();
            let stack = pushstack(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let space2 = heap_size();
            let now = Instant::now();
            popstack(stack, size);
            assert_eq!(heap_size(), space1);
            (
                time,
                now.elapsed().as_micros() as f64 * 0.001,
                space2 - space1,
            )
        };

        let pushqueue = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("queueInsertN");
        let popqueue = compiler.get_function::<unsafe extern "C" fn(u64, u64) -> ()>("queueTakeN");

        let mplqueue = |size| unsafe {
            let space1 = heap_size();
            let now = Instant::now();
            let queue = pushqueue(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let space2 = heap_size();
            let now = Instant::now();
            popqueue(queue, size);
            assert_eq!(heap_size(), space1);
            (
                time,
                now.elapsed().as_micros() as f64 * 0.001,
                space2 - space1,
            )
        };

        let pushvec = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("vecInsertN");
        let popvec = compiler.get_function::<unsafe extern "C" fn(u64, u64) -> ()>("vecTakeN");

        let mplvec = |size| unsafe {
            let space1 = heap_size();
            let now = Instant::now();
            let vec = pushvec(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let space2 = heap_size();
            let now = Instant::now();
            popvec(vec, size);
            assert_eq!(heap_size(), space1);
            (
                time,
                now.elapsed().as_micros() as f64 * 0.001,
                space2 - space1,
            )
        };

        let pushvec2 = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("vecInsertN2");
        let popvec2 = compiler.get_function::<unsafe extern "C" fn(u64, u64) -> ()>("vecTakeN2");

        let mplvec2 = |size| unsafe {
            let space1 = heap_size();
            let now = Instant::now();
            let vec = pushvec2(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let space2 = heap_size();
            let now = Instant::now();
            popvec2(vec, size);
            assert_eq!(heap_size(), space1);
            (
                time,
                now.elapsed().as_micros() as f64 * 0.001,
                space2 - space1,
            )
        };

        let rustslinkedlist = |size| {
            let now = Instant::now();
            let mut ll: LinkedList<u64> = LinkedList::new();
            for i in 0..size {
                ll.push_front(i);
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let now = Instant::now();
            let space = ll.get_size();
            for _ in 0..size {
                std::hint::black_box(ll.pop_front());
            }
            drop(ll);
            (time, now.elapsed().as_micros() as f64 * 0.001, space as u64)
        };

        let rustvecdeque = |size| {
            let now = Instant::now();
            let mut vd: VecDeque<u64> = VecDeque::new();
            for i in 0..size {
                vd.push_front(i);
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let space = vd.get_size();
            let now = Instant::now();
            for _ in 0..size {
                std::hint::black_box(vd.pop_front());
            }
            drop(vd);
            (time, now.elapsed().as_micros() as f64 * 0.001, space as u64)
        };

        let mut tpush = table!([H6c->"Push Benchmark"],[
            "Size",
            "MPL linked list FILO",
            "MPL linked list FIFO",
            "MPL map",
            //"MPL map 2",
            "Rust LinkedList",
            "Rust VecDeque",
        ]);
        let mut tpop = table!([H6c->"Pop Benchmark"],[
            "Size",
            "MPL linked list FILO",
            "MPL linked list FIFO",
            "MPL map",
            //"MPL map 2",
            "Rust LinkedList",
            "Rust VecDeque",
        ]);
        let mut space = table!([H6c->"Space Benchmark"],[
            "Size",
            "MPL linked list FILO",
            "MPL linked list FIFO",
            "MPL map",
            //"MPL map 2",
            "Rust LinkedList",
            "Rust VecDeque",
        ]);
        for p in 2..8 {
            let n = 10u64.pow(p);
            let (mplpushstack, mplpopstack, mplstackspace) = sum3(RUNS, || mplstack(n));
            let (mplpushqueue, mplpopqueue, mplqueuespace) = sum3(RUNS, || mplqueue(n));
            let (mplpushvec2, mplpopvec2, mplvec2space) = sum3(RUNS, || mplvec2(n));
            let (rustpushll, rustpopll, rustllspace) = sum3(RUNS, || rustslinkedlist(n));
            let (rustpushvecdeque, rustpopvecdeque, rustdequespace) =
                sum3(RUNS, || rustvecdeque(n));
            #[cfg(feature = "heapsize")]
            {
                space.add_row(row![
                    format!("10^{p}"),
                    format!("{:.2} B", mplstackspace / RUNS as u64),
                    format!("{:.2} B", mplqueuespace / RUNS as u64),
                    format!("{:.2} B", mplvec2space / RUNS as u64),
                    format!("{:.2} B", rustllspace / RUNS as u64),
                    format!("{:.2} B/key", rustdequespace / RUNS as u64),
                ]);
            }
            #[cfg(not(feature = "heapsize"))]
            {
                tpush.add_row(row![
                    format!("10^{p}"),
                    format!("{mplpushstack:.2}ms"),
                    format!("{mplpushqueue:.2}ms"),
                    //format!("{mplpushvec:.2}ms"),
                    format!("{mplpushvec2:.2}ms"),
                    format!("{rustpushll:.2}ms"),
                    format!("{rustpushvecdeque:.2}ms"),
                ]);
                tpop.add_row(row![
                    format!("10^{p}"),
                    format!("{mplpopstack:.2}ms"),
                    format!("{mplpopqueue:.2}ms"),
                    //format!("{mplpopvec:.2}ms"),
                    format!("{mplpopvec2:.2}ms"),
                    format!("{rustpopll:.2}ms"),
                    format!("{rustpopvecdeque:.2}ms"),
                ]);
            }
        }
        #[cfg(feature = "heapsize")]
        {
            space.printstd();
            let mut f = File::create("./benchmark/pushpop_space.txt").unwrap();
            _ = space.print(&mut f);
            f = OpenOptions::new()
                .write(true)
                .append(true)
                .open("./benchmark/pushpop_space.txt")
                .unwrap();
            _ = writeln!(f, "{}", table_to_latex_tabular_inner(space));
        }
        #[cfg(not(feature = "heapsize"))]
        {
            tpush.printstd();
            let mut f = File::create("./benchmark/push.txt").unwrap();
            _ = tpush.print(&mut f);
            f = OpenOptions::new()
                .write(true)
                .append(true)
                .open("./benchmark/push.txt")
                .unwrap();
            _ = writeln!(f, "{}", table_to_latex_tabular_inner(tpush));
            tpop.printstd();
            let mut f = File::create("./benchmark/pop.txt").unwrap();
            _ = tpop.print(&mut f);
            f = OpenOptions::new()
                .write(true)
                .append(true)
                .open("./benchmark/pop.txt")
                .unwrap();
            _ = writeln!(f, "{}", table_to_latex_tabular_inner(tpop));
        }
        Ok(())
    }

    fn tree() -> Result<(), ()> {
        let fp = parser::FileParser::new("./benchmark/tree.mpl").unwrap();
        let mut ast = fp.parse().unwrap();
        check(&mut ast);
        let context = Context::create();
        let builder = &context.create_builder();
        let module = &context.create_module("module");
        let compiler = compile::compile(&context, builder, module, ast);

        let heap_size = compiler.get_function::<unsafe extern "C" fn() -> u64>("heapSize");

        let tree_fill = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("BTreeFill");
        let tree_empty = compiler.get_function::<unsafe extern "C" fn(u64, u64)>("BTreeEmpty");
        let tree_free = compiler.get_function::<unsafe extern "C" fn(u64)>("BTreeFree");

        let mpltree = |size| unsafe {
            let space1 = heap_size();
            let mut now = Instant::now();
            let tree = tree_fill(size);
            let time1 = now.elapsed().as_micros() as f64 * 0.001;
            let space2 = heap_size();
            now = Instant::now();
            tree_empty(tree, size);
            let time2 = now.elapsed().as_micros() as f64 * 0.001;
            tree_free(tree);
            assert_eq!(space1, heap_size());
            (time1, time2, space2 - space1)
        };

        let rusttree = |size| {
            let mut now = Instant::now();
            let mut tree = None;
            let mut idx = 0;
            let mut val: u64 = size / 2;
            while idx < size {
                BinaryTree::insert(&mut tree, val % size);
                idx += 1;
                val = val.wrapping_mul(3).wrapping_add(idx);
            }
            let time1 = now.elapsed().as_micros() as f64 * 0.001;
            now = Instant::now();

            BinaryTree::print(&tree, 0);
            let space = tree.get_size() as u64;
            for i in 0..size {
                tree = BinaryTree::remove(tree, i);
            }
            let time2 = now.elapsed().as_micros() as f64 * 0.001;
            drop(tree);
            (time1, time2, space)
        };
        #[cfg(not(feature = "heapsize"))]
        let mut t = table!([H5c->"BinaryTree Benchmark"],[
            "Keys",
            "MPL insert",
            "MPL remove",
            "Rust insert",
            "Rust remove",
        ]);
        #[cfg(feature = "heapsize")]
        let mut t = table!([H3c->"BinaryTree Space Benchmark"],[
            "Keys",
            "MPL",
            "Rust",
        ]);
        for p in 2..7 {
            let n = 10u64.pow(p);
            let (pmltreeinsert, pmltreeremove, mplspace) = sum3(RUNS, || mpltree(n));
            let (rusttreeinsert, rusttreeremove, rustspace) = sum3(RUNS, || rusttree(n));
            #[cfg(feature = "heapsize")]
            t.add_row(row![
                format!("10^{p}"),
                format!("{:.2} B", mplspace / RUNS as u64),
                format!("{:.2} B", rustspace / RUNS as u64),
            ]);
            #[cfg(not(feature = "heapsize"))]
            t.add_row(row![
                format!("10^{p}"),
                format!("{pmltreeinsert:.2}ms"),
                format!("{pmltreeremove:.2}ms"),
                format!("{rusttreeinsert:.2}ms"),
                format!("{rusttreeremove:.2}ms"),
            ]);
        }
        #[cfg(not(feature = "heapsize"))]
        let path = "./benchmark/tree.txt";
        #[cfg(feature = "heapsize")]
        let path = "./benchmark/tree_space.txt";
        t.printstd();
        let mut f = File::create(path).unwrap();
        _ = t.print(&mut f);
        f = OpenOptions::new()
            .write(true)
            .append(true)
            .open(path)
            .unwrap();
        _ = writeln!(f, "{}", table_to_latex_tabular_inner(t));
        Ok(())
    }

    fn graph() -> Result<(), ()> {
        Ok(())
    }

    fn heap() -> Result<(), ()> {
        Ok(())
    }

    #[derive(Debug, GetSize)]
    pub struct BinaryTree<T> {
        pub value: T,
        pub left: Option<Box<BinaryTree<T>>>,
        pub right: Option<Box<BinaryTree<T>>>,
    }

    impl<T: Ord + Copy + Display> BinaryTree<T> {
        pub fn new(value: T) -> Self {
            BinaryTree {
                value,
                left: None,
                right: None,
            }
        }

        pub fn insert(s: &mut Option<Box<Self>>, insert_val: T) {
            match s {
                None => {
                    *s = Some(Box::new(BinaryTree {
                        value: insert_val,
                        left: None,
                        right: None,
                    }))
                }
                Some(s) => {
                    let mut current = s;
                    loop {
                        let BinaryTree {
                            ref mut left,
                            ref mut right,
                            ref mut value,
                        } = current.as_mut();
                        if *value > insert_val {
                            match left {
                                Some(l) => {
                                    current = l;
                                }
                                None => {
                                    *left = Some(Box::new(BinaryTree::new(insert_val)));
                                    return;
                                }
                            }
                        } else {
                            match right {
                                Some(l) => {
                                    current = l;
                                }
                                None => {
                                    *right = Some(Box::new(BinaryTree::new(insert_val)));
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }

        pub fn remove(mut s: Option<Box<Self>>, val: T) -> Option<Box<Self>> {
            match s.as_mut() {
                None => {}
                Some(root) => {
                    if val < root.value {
                        root.left = BinaryTree::remove(take(&mut root.left), val);
                    } else if val > root.value {
                        root.right = BinaryTree::remove(take(&mut root.right), val);
                    } else if root.left.is_none() && root.right.is_none() {
                        return None;
                    } else if root.left.is_none() {
                        *root = take(&mut root.right).unwrap();
                    } else if root.right.is_none() {
                        *root = take(&mut root.left).unwrap();
                    } else {
                        let mut r = take(&mut root.right).unwrap();
                        let l = take(&mut root.left).unwrap();
                        if r.left.is_none() {
                            *root = r;
                        } else {
                            let parrent = {
                                let mut l = &mut r;
                                while l.left.as_ref().unwrap().left.is_some() {
                                    l = l.left.as_mut().unwrap()
                                }
                                l
                            };
                            *root = take(&mut parrent.left).unwrap();
                            root.right = Some(r);
                        }
                        root.left = Some(l);
                    }
                }
            }
            s
        }

        pub fn print(s: &Option<Box<Self>>, indent: i32) {
            if s.is_none() {
                return;
            }
            let s = s.as_ref().unwrap();
            BinaryTree::print(&s.right, indent + 1);
            for _ in 0..indent {
                print!("\t")
            }
            println!("{}", s.value);
            BinaryTree::print(&s.left, indent + 1);
        }
    }
}

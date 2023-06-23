

#[cfg(test)]
mod tests {
    use inkwell::context::Context;
    use prettytable::{row, table};
    use std::{
        collections::{HashMap, HashSet, LinkedList, VecDeque},
        fs::File,
        mem::{swap, take},
        ops::Deref,
        time::Instant, fmt::Display, process::id, num::Wrapping,
    };

    use crate::{check, compile, parser};
    fn average(t: u64, f: impl Fn() -> f64) -> f64 {
        (0..t).map(|_| f()).sum::<f64>() / (t as f64)
    }
    fn average2(t: u64, f: impl Fn() -> (f64, f64)) -> (f64, f64) {
        (0..t).fold((0f64, 0f64), |mut acc, _| {
            let f = f();
            acc.0 += f.0;
            acc.1 += f.1;
            acc
        })
    }

    #[test]
    fn benchmark() -> Result<(), ()> {
        //fill()?;
        //lookup()?;
        //pushpop()?;
        tree()?;
        //graph()?;
        //heap()?;
		Err(())
    }

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
        let rustvec = |size| {
            let now = Instant::now();
            let mut m: Vec<u64> = Vec::with_capacity(0);
            for i in 0..size {
                m.push(std::hint::black_box(i));
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop(m);
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
        let mut t = table!([H7c->"Fill Benchmark"],[
            "Keys",
            "MPL set",
            "MPL map",
            "MPL set float",
            "Rust vec",
            "Rust set",
            "Rust map"
        ]);
        for p in 2..9 {
            let n = 10u64.pow(p);
            let runs = 1;
            t.add_row(row![
                //format!("{runs}"),
                format!("10^{p}"),
                format!("{:.2}ms", average(runs, || { mplset(n) })),
                format!("{:.2}ms", average(runs, || { mplmap(n) })),
                format!("{:.2}ms", average(runs, || { mplsetfloat(n) })),
                format!("{:.2}ms", average(runs, || { rustvec(n) })),
                format!("{:.2}ms", average(runs, || { rustset(n) })),
                format!("{:.2}ms", average(runs, || { rustmap(n) }))
            ]);
        }
        t.printstd();
        let mut f = File::create("./benchmark/fill.txt").unwrap();
        _ = t.print(&mut f);
        Ok(())
    }

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
            map_lookup(map, size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            drop_map(map);
            time
        };
        let rustmap = |size| {
            let mut map: HashMap<u64, u64> = HashMap::new();
            for i in (0..size).step_by(2) {
                std::hint::black_box(map.insert(i, i));
            }
            let now = Instant::now();
            let mut r = 0;
            for i in 0..size {
                if let Some(v) = map.get(&i) {
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
            "RUST map",
        ]);
        for p in 2..8 {
            let n = 10u64.pow(p);
            let runs = 4; //4u64.pow(8 - p);
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

    fn pushpop() -> Result<(), ()> {
        let fp = parser::FileParser::new("./benchmark/pushpop.mpl").unwrap();
        let mut ast = fp.parse().unwrap();
        check(&mut ast);
        let context = Context::create();
        let builder = &context.create_builder();
        let module = &context.create_module("module");
        let compiler = compile::compile(&context, builder, module, ast);

        let pushstack = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("stackInsertN");
        let popstack = compiler.get_function::<unsafe extern "C" fn(u64, u64) -> ()>("stackTakeN");

        let mplstack = |size| unsafe {
            let now = Instant::now();
            let stack = pushstack(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let now = Instant::now();
            popstack(stack, size);
            (time, now.elapsed().as_micros() as f64 * 0.001)
        };

        let pushqueue = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("queueInsertN");
        let popqueue = compiler.get_function::<unsafe extern "C" fn(u64, u64) -> ()>("queueTakeN");

        let mplqueue = |size| unsafe {
            let now = Instant::now();
            let queue = pushqueue(size);
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let now = Instant::now();
            popqueue(queue, size);
            (time, now.elapsed().as_micros() as f64 * 0.001)
        };

        let rustslinkedlist = |size| {
            let now = Instant::now();
            let mut ll: LinkedList<u64> = LinkedList::new();
            for i in 0..size {
                ll.push_front(i);
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let now = Instant::now();
            for _ in 0..size {
                std::hint::black_box(ll.pop_front());
            }
            drop(ll);
            (time, now.elapsed().as_micros() as f64 * 0.001)
        };

        let rustvecdeque = |size| {
            let now = Instant::now();
            let mut vd: VecDeque<u64> = VecDeque::new();
            for i in 0..size {
                vd.push_front(i);
            }
            let time = now.elapsed().as_micros() as f64 * 0.001;
            let now = Instant::now();
            for _ in 0..size {
                std::hint::black_box(vd.pop_front());
            }
            drop(vd);
            (time, now.elapsed().as_micros() as f64 * 0.001)
        };

        let mut t = table!([H7c->"Stack Benchmark"],[
            "Size",
            "MPL push (linked list FILO)",
            "MPL pop (linked list FILO)",
            "MPL push (linked list FIFO)",
            "MPL pop (linked list FIFO)",
            //"MPL push (Deque)", TODO
            //"MPL pop (Deque)",
            "Rust push (linked list)",
            "Rust pop (linked list)",
            "Rust push (VecDeque)",
            "Rust pop (VecDeque)",
        ]);
        for p in 2..8 {
            let n = 10u64.pow(p);
            let runs = 1;
            let (mplpushstack, mplpopstack) = average2(runs, || mplstack(n));
            let (mplpushqueue, mplpopqueue) = average2(runs, || mplqueue(n));
            let (rustpushll, rustpopll) = average2(runs, || rustslinkedlist(n));
            let (rustpushvecdeque, rustpopvecdeque) = average2(runs, || rustvecdeque(n));
            t.add_row(row![
                format!("10^{p}"),
                format!("{mplpushstack:.2}ms"),
                format!("{mplpopstack:.2}ms"),
                format!("{mplpushqueue:.2}ms"),
                format!("{mplpopqueue:.2}ms"),
                format!("{rustpushll:.2}ms"),
                format!("{rustpopll:.2}ms"),
                format!("{rustpushvecdeque:.2}ms"),
                format!("{rustpopvecdeque:.2}ms"),
            ]);
        }
        t.printstd();
        let mut f = File::create("./benchmark/pushpop.txt").unwrap();
        _ = t.print(&mut f);

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

        let tree_fill = compiler.get_function::<unsafe extern "C" fn(u64) -> u64>("BTreeFill");
        let tree_empty = compiler.get_function::<unsafe extern "C" fn(u64, u64)>("BTreeEmpty");
        let tree_free = compiler.get_function::<unsafe extern "C" fn(u64)>("BTreeFree");

        let mpltree = |size| unsafe {
            let mut now = Instant::now();
            let tree = tree_fill(size);
            let time1 = now.elapsed().as_micros() as f64 * 0.001;
            now = Instant::now();
            tree_empty(tree, size);
            let time2 = now.elapsed().as_micros() as f64 * 0.001;
            tree_free(tree);
            (time1, time2)
        };

        let rusttree = |size| {
            let mut now = Instant::now();
			let mut tree = None;
			let mut idx = 0;
			let mut val: u64 = size/2;
			while idx < size {
				BinaryTree::insert(&mut tree, val % size);
				idx+=1;
				val = val.wrapping_mul(3).wrapping_add(idx);
			}
            let time1 = now.elapsed().as_micros() as f64 * 0.001;
            now = Instant::now();
            BinaryTree::print(&tree, 0);
			for i in 0..size {
				println!("#{i}");
				tree = BinaryTree::remove(tree, i);
				BinaryTree::print(&tree, 0);
			}
            let time2 = now.elapsed().as_micros() as f64 * 0.001;
            drop(tree);
            (time1, time2)
        };
		rusttree(20);

        let mut t = table!([H5c->"BinaryTree Benchmark"],[
            "Keys",
            "MPL Tree insert",
            "MPL Tree remove",
            "Rust insert",
            "Rust remove",
        ]);
        for p in 2..3 {
            let n = 10u64.pow(p);
            let runs = 1;
            let (pmltreeinsert, pmltreeremove) = average2(runs, || mpltree(n));
			//let (rusttreeinsert, rusttreeremove) = average2(runs, || rusttree(n));
            t.add_row(row![
                format!("10^{p}"),
                format!("{pmltreeinsert:.2}ms"),
                format!("{pmltreeremove:.2}ms"),
				//format!("{rusttreeinsert:.2}ms"),
                //format!("{rusttreeremove:.2}ms"),
                //format!("{:.2}ms", average(runs, || { rustmap(n) })),
            ]);
        }
        t.printstd();
        let mut f = File::create("./benchmark/tree.txt").unwrap();
        _ = t.print(&mut f);

        Ok(())
    }

    fn graph() -> Result<(), ()> {
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

        let mut t = table!([H3c->"Lookup Benchmark 50% Hit"],[
            "Keys",
            "MPL map",
            "RUST map",
        ]);
        for p in 2..8 {
            let n = 10u64.pow(p);
            let runs = 4;
            t.add_row(row![
                format!("10^{p}"),
                //format!("{:.2}ms", average(runs, || { mplmap(n) })),
                //format!("{:.2}ms", average(runs, || { rustmap(n) })),
            ]);
        }
        t.printstd();
        let mut f = File::create("./benchmark/lookup.txt").unwrap();
        _ = t.print(&mut f);

        Ok(())
    }

    fn heap() -> Result<(), ()> {
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

        let mut t = table!([H3c->"Lookup Benchmark 50% Hit"],[
            "Keys",
            "MPL map",
            "RUST map",
        ]);
        for p in 2..8 {
            let n = 10u64.pow(p);
            let runs = 4;
            t.add_row(row![
                format!("10^{p}"),
                //format!("{:.2}ms", average(runs, || { mplmap(n) })),
                //format!("{:.2}ms", average(runs, || { rustmap(n) })),
            ]);
        }
        t.printstd();
        let mut f = File::create("./benchmark/lookup.txt").unwrap();
        _ = t.print(&mut f);
        Ok(())
    }

	#[derive(Debug)]
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

        pub fn insert(s: &mut Option<Box<Self>>, new_value: T) {
            match s {
                None => {
                    *s = Some(Box::new(BinaryTree {
                        value: new_value,
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
                        if new_value <= *value {
                            match left {
                                Some(l) => {
                                    current = l;
                                }
                                None => {
                                    *left = Some(Box::new(BinaryTree::new(new_value)));
                                    return;
                                }
                            }
                        } else {
                            match right {
                                Some(l) => {
                                    current = l;
                                }
                                None => {
                                    *right = Some(Box::new(BinaryTree::new(new_value)));
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
						*root=take(&mut root.right).unwrap();
                    } else if root.right.is_none() {
						*root=take(&mut root.left).unwrap();
                    }else{
						let mut r = take(&mut root.right).unwrap();
						let l = take(&mut root.left).unwrap();
						if r.left.is_none(){
							*root = r;
						}else{
							let parrent = {
								let mut l = &mut r;
								while l.left.as_ref().unwrap().left.is_some(){
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
			if s.is_none(){
				return;
			}
			let s = s.as_ref().unwrap();
			BinaryTree::print(&s.right, indent+1);
			for i in 0..indent {
				print!("\t")
			}
			println!("{}",s.value);
			BinaryTree::print(&s.left, indent+1);
		}
	}
	
}

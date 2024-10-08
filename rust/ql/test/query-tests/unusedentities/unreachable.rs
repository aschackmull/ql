
//fn cond() -> bool;
//fn get_a_number() -> i32;

// --- unreachable code --

fn do_something() {
}

fn unreachable_if() {
	if false {
		do_something(); // BAD: unreachable code [NOT DETECTED]
	} else {
		do_something();
	}

	if true {
		do_something();
	} else {
		do_something(); // BAD: unreachable code [NOT DETECTED]
	}

	let v = get_a_number();
	if v == 1 {
		if v != 1 {
			do_something(); // BAD: unreachable code [NOT DETECTED]
		}
	}

	if cond() {
		return;
		do_something(); // BAD: unreachable code
	}

	if cond() {
		do_something();
	} else {
		return;
		do_something(); // BAD: unreachable code
	}
	do_something();

	if cond() {
		return;
	} else {
		return;
	}
	do_something(); // BAD: unreachable code
}

fn unreachable_panic() {
	if cond() {
		do_something();
		panic!("Oh no!!!");
		do_something(); // BAD: unreachable code [NOT DETECTED]
	}

	if cond() {
		do_something();
		unimplemented!();
		do_something(); // BAD: unreachable code [NOT DETECTED]
	}

	if cond() {
		do_something();
		todo!();
		do_something(); // BAD: unreachable code [NOT DETECTED]
	}

	if cond() {
		let mut maybe;

		maybe = Some("Thing");
		_ = maybe.unwrap(); // (safe)
		do_something();

		maybe = if cond() { Some("Other") } else { None };
		_ = maybe.unwrap(); // (might panic)
		do_something();

		maybe = None;
		_ = maybe.unwrap(); // (always panics)
		do_something(); // BAD: unreachable code [NOT DETECTED]
	}

	if cond() {
		do_something();
		_ = false && panic!(); // does not panic due to short-circuiting
		do_something();
		_ = false || panic!();
		do_something(); // BAD: unreachable code [NOT DETECTED]
	}

	if cond() {
		do_something();
		_ = true || panic!(); // does not panic due to short-circuiting
		do_something();
		_ = true && panic!();
		do_something(); // BAD: unreachable code [NOT DETECTED]
	}
}

fn unreachable_match() {
	match get_a_number() {
		1=>{ // [unreachable FALSE POSITIVE]
			return;
		}
		_=>{ // [unreachable FALSE POSITIVE]
			do_something();
		}
	}
	do_something(); // [unreachable FALSE POSITIVE]

	match get_a_number() {
		1=>{ // [unreachable FALSE POSITIVE]
			return;
		}
		_=>{ // [unreachable FALSE POSITIVE]
			return;
		}
	}
	do_something(); // BAD: unreachable code
}

fn unreachable_loop() {
	loop {
		do_something();
		break;
		do_something(); // BAD: unreachable code
	}

	if cond() {
		while cond() {
			do_something();{ // [unreachable FALSE POSITIVE]
		}

		while false {
			do_something(); // BAD: unreachable code
		}

		while true {
			do_something(); // [unreachable FALSE POSITIVE]
		}
		do_something(); // BAD: unreachable code [NOT DETECTED]
	}

	loop {
		if cond() {
			return;
			do_something(); // BAD: unreachable code
		}
	}
	do_something(); // BAD: unreachable code
	do_something();
	do_something();
}

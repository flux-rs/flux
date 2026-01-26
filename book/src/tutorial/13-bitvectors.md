# Dependent Typestates

```rust, editable, hidden
use std::{
  mem::replace,
  sync::atomic::{AtomicBool, Ordering}, vec,
};

use flux_rs::{
    assert, alias, constant, defs, macros::detached_spec, extern_spec, invariant, opaque, refined_by, reflect, spec, specs, trusted,
    bitvec::BV32;
};
```

Our next case study shows how Flux’s refinements can be used to make the
_typestate_ even more expressive by connecting typestates with run-time
values to avoiding the blowup that ensues from using (only) Rust’s types
[^1] while still providing compile-time correctness guarantees. Lets
explore this idea by building a library to manipulate GPIO pins on
embedded hardware where each _port_ comprises multiple _pins_ each of
which can be set to be in `Input` or `Output` mode, and must be used
according to its current mode.

## Bitvectors

The pins” modes will be configured and accessed via _bitwise_ operations
on dedicated hardware registers. Flux lets us precisely track the
results of bitwise operations — just like we can track arithmetic
operations (\[ch\]:02_refinements) or set operations (\[ch\]:12_sets) —
with a special `flux_rs::bitvec::BV32` type that represents 32-bit
bitvectors as an _opaque_ (see [this chapter](ch06_vectors).md) newtype wrapper around
`u32` indexed by a `bitvec<32>` that tracks the bits of the underlying
`u32` [^2].

```rust
#[refined_by(x: bitvec<32>)]        // bitvector-valued index
pub struct BV32(u32);
```

### Creating and Operating on Bitvectors

The API for `BV32` has methods to convert from and to `u32` whose refine
contracts use the _logical functions_ `bv_int_to_bv32` and
`bv_bv32_to_int` to convert between the `int` index (of the `u32`) and
its `bitvec<32>` representation (of the `BV32`).

```rs
impl BV32 {
  #[spec(fn(value: u32) -> BV32[bv_int_to_bv32(value)])]
  pub fn new(value: u32) -> BV32 { BV32(value) }
}
```

```rs
impl Into<u32> for BV32 {
  #[spec(fn(self:BV32) -> u32[bv_bv32_to_int(self)])]
  pub fn into(self) -> u32 { self.0 }
}
```

**Bitvector Operations** The `flux_rs::bitvec` library implements the
various traits like `BitAnd`, `BitOr`, `Not`, `Shl`, `Shr`, _etc._ to
enable bitwise operations on `BV32` values. For example, the
_left-shift_ (`<<`) operation is implemented as

```rust
impl Shl<u32> for BV32 {
  #[spec(fn(self, rhs: u32) -> BV32[self << bv_int_to_bv32(rhs)])]
  fn shl(self, rhs: u32) -> BV32 { BV32(self.0 << rhs) }
}
```

and the bitwise or (`|`) operation is implemented as

```rust
impl BitOr for BV32 {
  #[spec(fn(self, rhs: BV32) -> BV32[self | rhs])]
  fn bitor(self, rhs: BV32) -> BV32 { BV32(self.0 | rhs.0) }
}
```

**EXERCISE:** Lets test our operators out: can you fix the code below so
the `assert` is verified by Flux?

```rust, editable
#[spec(fn () -> u32[10])]
fn test_shl_or() {
  let b1 = BV32::new(1);  // 0b0001
  let b5 = BV32::new(5);  // 0b0101
  let res = b5 << b1;     // 0b1010
  let res = res | b1;     // 0b1011
  res.into()
}
```

### Getting and Setting Individual Bits

Next, lets use the bitwise operations to write functions that _get_ or
_set_ a bit at a particular position in a `BV32`.

**Valid Bit Positions** Lets first write an alias for valid bit
positions (`0` to `31`)

```rust, editable
#[alias(type Pin = u8{n: 0 <= n && n < 32})]
type Pin = u8;
```

Note that while `rustc` will allow any `u8` value to be used as a `Pin`,
Flux will complain if we try to use a value outside the valid range.

**Getting the Value of a Pin** We can now write a function that _gets_
the value of a `BV32` at a given position by returning `true` if the bit
is set to `1` and `false` otherwise.

```rust, editable
fn get_pin(bv: BV32, pin: Pin) -> bool {
    ((bv >> pin) & 1) == b1
}
```

**Setting the Value of a Pin** Similarly, we can write a function that
takes as input a `bool` and _sets_ the bit at the given position to `1`
if the `bool` is `true` and to `0` otherwise.

```rust, editable
fn set_pin(bv:BV32, pin:Pin, b:bool) -> BV32 {
    if b {
        bv | (BV32::new(1) << pin)
    } else {
        bv & !(BV32::new(1) << pin)
    }
}
```

**Refinement-Level Get/Set Functions** To verify code that _uses_
`get_pin` and `set_pin`, we need to specify their behavior using Flux
contracts. The most direct way to do so is to write _refinement
functions_ (see [this chapter](ch04_structs.md#refinement-functions)) like `get_pin`,
defined below

```rust, editable
defs! {
    fn get_pin(bv: bitvec<32>, pin: int) -> bool{
        let val = (bv >> bv_int_to_bv32(pin)) & 1;
        val == 1
    }
}
```

and `set_pin` which is similarly defined as shown below

```rust, editable
defs! {
    fn set_pin(bv: bitvec<32>, pin: int, val: bool) -> bitvec<32> {
        let index_bits = bv_int_to_bv32(pin);
        if val {
            bv | (1 << index_bits)
        } else {
            bv & bv_not(1 << index_bits)
        }
    }
}
```

**Syntax:** While we have tried to make the syntax of the _refinement
function_ `set_pin` shown above _look like_ the implementation of the
Rust method of the same name, they are not the same thing. Indeed,
notice we wrote `bv_not` instead of `!` in the refinement function as
`!` is reserved for boolean negation inside refinement expressions.

**Connecting Rust Methods with Refinement Functions** Once we have
defined the refinement functions, we can use them to specify the output
types of the corresponding Rust functions, using detached specifications
(see [this chapter](ch11_equality.md#detached)).

```rust, editable
detached_spec! {
  fn get_pin(bv: BV32, pin: Pin) -> bool[get_pin(bv, pin)];
  fn set_pin(bv: BV32, pin: Pin, b: bool) -> BV32[set_pin(bv, pin, b)];
}
```

We can confirm that the specifications for the above are correctly
tracking the bits via the following test:

```rust, editable
fn test_get_set_pin() {
  let b5 = BV32::new(5);            // 0b0101
  flux_rs::assert(get_pin(b5, 2));  // bit 2 is set
  let b5 = set_pin(b5, 2, false);   // 0b0001
  flux_rs::assert(!get_pin(b5, 2)); // bit 2 is cleared
}
```

## GPIO Ports

Lets tuck the newly learned information about bitvectors into our
pockets and now turn to the issue at hand: developing an API for
interacting with _General Purpose Input/Output_ (GPIO) _ports_ in
low-level embedded microcontrollers.

**Ports and Pins** GPIO ports are the conduit through which
microcontrollers “talk” to the external world, _e.g._ to read sensors
that determine key-presses or light up output LEDs. GPIO ports, are
themselves collections of _pins_ that can be configured individually as
either `Input` or `Output`, and which can then be read from or written
to accordingly. The developer must take care to use each pin according
to how it’s mode was configured, as otherwise the hardware may produce
invalid data or worse, may destroy the hardware by releasing its “magic
smoke” [^3]!

**Registers** In common hardware platforms like the STM32, ports are
controlled via dedicated _memory mapped port registers_ which control
the modes and input and output values of _all_ the pins in that port,
where the i<sup>th</sup> bit in the register corresponds to the
i<sup>th</sup> pin of the port. We can model such registers in Rust as

```rust, editable
#[repr(C)]
struct Registers {
  modes: BV32, // Bit 0 = pin 0 mode, bit 1 = pin 1 mode, etc.
  output: u32, // Bit 0 = pin 0 output, bit 1 = pin 1 output, etc.
  input: u32,  // Bit 0 = pin 0 input, bit 1 = pin 1 input, etc.
}
```

and then the GPIO port itself is a wrapper around a pointer to such
registers

```rust, editable
struct Gpio(*mut Registers);
```

## Tracking Modes

If you are well-caffeinated, you may have noticed that we used the
`BV32` type for the `modes` register in `Registers` struct above, as it
will let us index the `struct Registers` with a `bitvec<32>` that tracks
the modes of all 32 pins in the GPIO port.

```rust, editable
detached_spec! {
  #[refined_by(modes: bitvec<32>)]
  struct Registers {
    modes: BV32[modes],
    output: u32,
    input: u32,
  }
}
```

Similarly, lets refine `struct Gpio` to track the `modes` of the
`Registers` that it _points to_

```rust, editable
#[refined_by(modes: bitvec<32>)]
  #[opaque] struct Gpio;
}
```

**Private Trusted API** As the actual `Registers` must be accessed
directly via `unsafe` pointer dereferences, we mark the `struct` as
`opaque` (see [this chapter](ch06_vectors).md) and write a small suite of _private_
`trusted` (_i.e._ unverified) methods for the `unsafe` dereferences,
that we will then use to to build a verified _public_ API for port
access.

```rust, editable
#[trusted]
impl Gpio {
    #[spec(fn(&Gpio[@modes]) -> &Registers[modes])]
    fn get_registers(&self) -> &Registers {
        unsafe { &*self.0 }
    }

    #[spec(fn(self: &mut Gpio, m: BV32) ensures self: Gpio[m])]
    fn set_modes(&mut self, m: BV32) {
        unsafe { (&mut *self.0).modes = m}
    }

    #[spec(fn(self:&mut Gpio[@m], output:u32) ensures self: Gpio[m])]
    fn set_output(&mut self, output: u32) {
        unsafe { (&mut *self.0).output = output }
    }
}
```

The `get_registers` dereferences the pointer stashed inside the `Gpio`
to return a `Registers` that has exactly the same `modes`. Dually, the
`set_modes` updates the `modes` of the underlying `Registers` with the
given value, updating the refinement of the `Gpio` accordingly. Finally,
the `set_output` updates the `output` register pointed to by the `Gpio`
but leaves the `modes` unchanged.

**Peripherals** Finally, we can bundle multiple GPIO ports into a
`Peripherals` struct that represents all the hardware peripherals of a
microcontroller.

```rust, editable
struct Peripherals { gpio_a: Gpio, gpio_b: Gpio, gpio_c: Gpio }
```

We can then provide safe singleton access to the peripherals via a
`take_peripherals` function that maps the actual addresses of the
hardware registers to `Gpio` instances.

```rust, editable
#[trusted]
fn take_peripherals() -> Option<Peripherals> {
  static TAKEN: AtomicBool = AtomicBool::new(false);
  if TAKEN
     .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
     .is_ok()
  { Some(Peripherals {
        gpio_a: Gpio(0x4800_0000 as *mut Registers),
        gpio_b: Gpio(0x4800_0400 as *mut Registers),
        gpio_c: Gpio(0x4800_0800 as *mut Registers),
    })
  } else { None }
}
```

## Using Modes

Next, lets use the private methods to implement a public API for GPIO
access that _gets_ and _sets_ a pin’s modes, and ensures it is used
according to its mode. First, lets write an `enum` to represent the
modes of a `Pin`

```rust, editable
#[reflect] #[derive(PartialEq, Eq)]
enum Mode { Input, Output }
flux_core::eq!(Mode);
```

We _could_ have just used `bool` but sadly, I kept mixing up whether
`true` meant `Input` or `Output`. An `enum` rather dispels the
confusion! However it will be quite convenient to convert between `Mode`
and `bool` with two helper functions

```rust, editable
impl From<bool> for Mode {
    #[spec(fn (b: bool) -> Mode[bool_to_mode(b)])]
    fn from(b: bool) -> Self {
        if b { Mode::Output } else { Mode::Input }
    }
}
impl Into<bool> for Mode {
    #[spec(fn (mode: Mode) -> bool[mode_to_bool(mode)])]
    fn into(self) -> bool {
        match self {
            Mode::Output => true,
            Mode::Input => false,
        }
    }
}
```

whose specifications use the refinement functions

```rust, editable
defs! {
  fn bool_to_mode(b:bool) -> Mode {
    if b {
        Mode::Output
    } else {
        Mode::Input
    }
  }

  fn mode_to_bool(mode: Mode) -> bool {
    mode == Mode::Output
  }
}
```

**Getting the Mode** Lets use the private API and the bitvector helpers
to implement a public method to get a `Pin`‘s mode, using `get_pin`
defined earlier plus the `Mode`-`bool` conversion.

```rust, editable
impl Gpio {
  #[spec(fn(&Gpio[@modes], pin: Pin) -> Mode[get_mode(modes, pin)])]
  pub fn get_mode(&self, pin: Pin) -> Mode {
    Mode::from(get_pin(self.get_registers().modes, pin))
  }
}
```

where the specification function `get_mode` is just

```rust, editable
defs! {
    fn get_mode(bv: bitvec<32>, index: int) -> Mode {
        bool_to_mode(get_pin(bv, index))
    }
}
```

**Setting the Mode** Similarly, we can implement a public method to set
a `Pin`‘s mode using `set_pin` defined earlier plus the `Mode`-`bool`
conversion.

```rust, editable
impl Gpio {
  // #[spec(EXERCISE)]
  pub fn set_mode(&mut self, pin: Pin, mode: Mode) {
    let regs = self.get_registers();
    self.set_modes(set_pin(regs.modes, pin, mode.into()))
  }
}
```

**EXERCISE:** Write the specification for `set_mode` so Flux verifies
`test_get_set`.

```rust, editable
#[spec(fn(gpio: &mut Gpio[@modes]) ensures gpio: Gpio[modes])]
fn test_get_set(gpio: &mut Gpio) {
    let orig = gpio.get_mode(3);              // save original mode
    gpio.set_mode(3, Mode::Output);           // set to output
    assert(gpio.get_mode(3) == Mode::Output); // verify mode
    gpio.set_mode(3, orig);                   // restore original mode
}
```

**Input and Output Pins** We want the methods that read from and write
to a `Pin` to only be invoked on pins that are configured to be in
`Input` or `Output` mode respectively. First, lets write a type _alias_
for such pins (as always, paired with a matching Rust-level alias that
can be used in Rust signatures.)

```rust, editable
#[alias(type In(m:bitvec<32>) = Pin{v:get_mode(m, v) == Mode::Input})]
type In = Pin;

#[alias(type Out(m:bitvec<32>) = Pin{v:get_mode(m, v) == Mode::Output})]
type Out = Pin;
```

**Dependent Aliases**: Unlike the definition of `Pin` which is simply a
`u8` between `0` and `32`, the definitions of the aliases `In` and `Out`
_depend on_ the `bitvec<32>` index `m`. This is essential as actual
_mode_ is stored in the `modes` register and not the `Pin` itself. Flux
supports such _dependent aliases_ with _alias parameters_ like
`m: bitvec<32>` that can be used in the alias body, and which must then
be supplied wherever the aliases are used in Flux specifications.

**Reading & Writing Pins** Finally, lets use the alias to write `read`
and `write` methods that only accept `In` and `Out` pins, respectively

```rust, editable
impl Gpio {
    #[spec(fn(&Gpio[@modes], pin: In(modes)) -> bool)]
    pub fn read(&self, pin: In) -> bool {
        let regs = self.get_registers();
        get_pin(regs.input.into(), pin)
    }

    #[spec(fn(self: &mut Gpio[@modes], pin: Out(modes), value: bool))]
    pub fn write(&mut self, pin: Out, value: bool) {
        let output = self.get_registers().output.into();
        let new_output = set_pin(output, pin, value).into();;
        self.set_output(new_output);
    }
}
```

Well then, we now have a complete API to determine and configure the
modes of each pin, and read and write them according to their enabled
modes, such that that Flux can statically ensure that the “magic smoke”
stays inside!

## Clients

Lets test our API out with some example client code.

**Reading and Writing Pins** Here’s an example that illustrates how we
can use our GPIO API to configure and access different pins on different
ports. First, we get mutable access to the GPIO ports via the
`take_peripherals` function. Next, we configure some pins as `Output`
and others as `Input`. Flux will use the specification for `set_mode` to
track each of the pins” modes separately (in the `modes` index for
`gpio_a` and `gpio_b`). Consequently, Flux will allow us to `read` from
the `Input` pins, and `write` to the `Input` pins. However, Flux will
prevent you from trying to `read` from or `write` to an `Output` or
`Input` pin, respectively, as you can see by uncommenting the lines at
the bottom of the function.

```rust, editable
fn test_read_write() {
    // Get mutable access to GPIOA
    let mut peripherals = take_peripherals().expect("taken!");
    let gpio_a = &mut peripherals.gpio_a;
    let gpio_b = &mut peripherals.gpio_b;

    // Different pins, different states
    gpio_a.set_mode(0, Mode::Output); // PA0 : Out
    gpio_a.set_mode(1, Mode::Output); // PA1 : Out
    gpio_a.set_mode(5, Mode::Input);  // PA5 : In
    gpio_b.set_mode(0, Mode::Input);  // PB3 = In

    // Valid accesses
    gpio_a.write(0, true);
    gpio_a.write(1, true);
    let button_state = gpio_a.read(5);
    let timer_state = gpio_b.read(0);

    // Invalid accesses caught at compile-time
    // gpio_a.read(0);         // ERROR! Can't read from Out pin
    // gpio_a.write(5, true);  // ERROR! Can't write to In pin
}
```

**Reading Multiple Pins** Your turn! Consider the function below that
takes as input _sequence_ of Pins, and returns as output a vector of the
`bool` obtained from reading the sequence of `Pins`.

**EXERCISE:** Write a `spec` that lets Flux verify `read_pins`.

```rust, editable
fn read_pins(gpio: &Gpio, pins: &[Pin]) -> Vec<bool> {
    let mut res = vec![];
    for pin in pins {
        res.push(gpio.read(*pin));
    }
    res
}
```

**Writing Multiple Pins** And here is a similar function that
additionally takes as input a sequence of `bool` values to write to the
corresponding sequence of `Pins`.

**EXERCISE:** Write a `spec` that lets Flux verify `write_pins`.

```rust, editable
fn write_pins(gpio: &mut Gpio, pins: &[Pin], vals: &[bool]) {
    for i in 0..pins.len() {
        gpio.write(pins[i], vals[i]);
    }
}
```

**Dynamic Mode Configuration** Lets look at an example where we might
want to “force” a `Pin` to `Output` mode, optionally returning its value
if it was (previously) in `Input` mode. Flux will not let us read from a
pin until we have established that the current mode (obtained by
`get_mode`) is, in fact, `Input`. At that point, we can read the pin,
and then set it to `Output` mode.

```rust, editable
#[spec(fn(gpio: &mut Gpio, pin:Pin) -> Option<bool> ensures gpio: Gpio)]
fn detect_and_set(gpio: &mut Gpio, pin: Pin) -> Option<bool> {
    // gpio.read(pin); // ERROR can't read, don't know state!
    if let Mode::Input = gpio.get_mode(pin) {
        let val = gpio.read(pin);
        gpio.set_mode(pin, Mode::Output);
        return Some(val);
    }
    None
}
```

**Blinking a Status LED** One often wants an embedded device to blink,
_e.g._ to let us know its alive and kicking. The usual maneuver is to
toggle a dedicated status LED pin inside the main loop of the
application.

**EXERCISE:** Fix the spec so Flux verifies `blink_status_led`.

```rust, editable
#[spec(fn(gpio: &mut { Gpio[@modes] | true}))]
fn blink_status_led(gpio: &mut Gpio) {
    static mut LED_STATE: bool = true;
    let value = unsafe { LED_STATE = !LED_STATE; LED_STATE };
    gpio.write(13, value); // HINT: When is this ok to call?
}
```

**EXERCISE:** Here’s the main “loop” of an embedded application that
blinks the status LED to indicate the system is alive. Can you find out
why Flux rejects the call to `blink_status_led`, and remedy mattes so
that `app` is accepted?

```rust, editable
fn app() {
    let mut peripherals = take_peripherals().expect("taken!");
    let gpio_c = &mut peripherals.gpio_c;
    // blink_status_led(gpio_c); // ERROR! not yet Output
    detect_and_set(gpio_c, 13); // ensure pin 13 is Output
    loop {
        // let result = process_data(read_sensors());
        // update_outputs(result);
        blink_status_led(gpio_c); // indicate system is alive
    }
}
```

## Summary

In this chapter, we learned about Flux’s support for _bitvector_ valued
refinements via the `BV` type, and how to use bitvectors to track the
modes of GPIO pins, to write a verified GPIO library that ensures pins
are used per their configuration.

Existing embedded Rust libraries track pin modes in Rust’s using
`PhantomData` and the typestate pattern [^4]. While this approach has
the advantage of working out of the box with plain `rustc`, it has two
drawbacks. First, we get a explosion in the number of types, and the
attendant duplication of methods. Second, and perhaps more
importantantly, we end up tracking the state of the `Pin` at the
type-level, when we really want to track state of the `modes` register
to avoid any shenanigans that might arise _concurrently_ accessing
different pins of the same port. (The classic typestate approach would
end up having to create 2<sup>32</sup> different types to track all mode
configurations of a single port!)

In contrast, Flux’s refinements allow us to compactly track the entire
vector of modes via logical refinements while still providing
compile-time guarantees that each pin is used according to its
configured mode.

[^1]: See <https://www.ecorax.net/macro-bunker-1/>

[^2]:
    Flux also supports `BV8`, `BV16` and `BV64` types for 8-, 16- and
    64-bit bitvectors, but lets focus on `BV32` for simplicity

[^3]: <https://en.wikipedia.org/wiki/Magic_smoke>

[^4]: <https://docs.rust-embedded.org/book/static-guarantees/state-machines.html>

mod iface {
    pub trait Receive {
        fn receive_buffer(&self);
    }

    pub trait UartData: Receive {}
}

mod driver {
    use super::iface::{Receive, UartData};

    pub struct MyUart;

    impl Receive for MyUart {
        fn receive_buffer(&self) {}
    }

    impl UartData for MyUart {}
}

use iface::UartData;

#[flux::no_panic]
fn foo(x: &dyn UartData) {
    let clos = || {
        x.receive_buffer();
    };
}

fn main() {}

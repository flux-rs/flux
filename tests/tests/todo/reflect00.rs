



#[flux_rs::reflect]
enum State {
    On,
    Off,
}


#[flux_rs::sig(fn () -> State[State::On])]
fn test00() -> State { 
    State::On
}


#[flux_rs::sig(fn () -> State[State::Off])]
fn test01() -> State { 
    State::Off
}

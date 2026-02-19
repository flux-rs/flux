mod bob {

    static BOB: usize = 43;

    fn test1() -> usize {
        BOB //~ ERROR: refinement type
    }

    static ARR: [usize; 3] = [1, 2, 3];

    fn test2() -> usize {
        ARR[0] + ARR[1] + ARR[2] //~ ERROR: refinement type
    }
}

#[flux::specs {

    mod bob {
        static BOB: usize[43];

        fn test1() -> usize[42];

        static ARR: [usize{v:v < 50}; 3];

        fn test2() -> usize{v:v<30};
    }

}]
const _: () = ();

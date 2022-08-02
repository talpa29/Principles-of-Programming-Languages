let map = {'a': 1, 'b': 2 };
map.a = 5;
console.log(map)

const f = (r: number, g: (x: number) => number): number => g(r - 1);


let t = 10
console.log(f(10, x => x * x))
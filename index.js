let message = process.argv[2];

/*
* Convert a 32-bit number to a hex string with ls-byte first
*/
function number_to_hex(num)
{
	let str = "";
	var hex_chr = "0123456789abcdef";
	for(j = 0; j <= 3; j++)
		str += hex_chr.charAt((num >> (j * 8 + 4)) & 0x0F) + hex_chr.charAt((num >> (j * 8)) & 0x0F);
	return str;
}

/*
* Convert a string to a sequence of 16-word blocks, stored as an array.
* Append padding bits and the length, as described in the MD5 standard.
*/

let rotate_left = (n, c) => (n << c) | (n >>> (32 - c));

function common_step(q, a, b, x, s, t)
{
	return rotate_left(((a + q) +  (x + t)), s) + b;
}
function step_one(a, b, c, d, x, s, t)
{
	return common_step((b & c) | ((~b) & d), a, b, x, s, t);
}
function step_two(a, b, c, d, x, s, t)
{
	return common_step((b & d) | (c & (~d)), a, b, x, s, t);
}
function step_three(a, b, c, d, x, s, t)
{
	return common_step(b ^ c ^ d, a, b, x, s, t);
}
function step_four(a, b, c, d, x, s, t)
{
	return common_step(c ^ (b | (~d)), a, b, x, s, t);
}

let constantes = [
	0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
	0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
	0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
	0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,

	0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
	0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
	0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
	0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,

	0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
	0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
	0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
	0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,

	0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
	0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
	0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
	0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
]
let div_4 = x => Math.floor(x / 4);

function str_to_blocks(str)
{
	let nblk = (Math.floor((str.length + 8) / 64)) + 1;
	let blocks = new Array(nblk * 16);
	for(i = 0; i < nblk * 16; i++)
		blocks[i] = 0;
	for(i = 0; i < str.length; i++)
		blocks[div_4(i)] |= str.charCodeAt(i) << ((i % 4) * 8);
	return blocks;
}


function md5(str)
{
	let x = str_to_blocks(str);
	x[div_4(str.length)] |= 0x80 << ((str.length % 4) * 8);
	x[((Math.floor((str.length + 8) / 64)) + 1 * 16) - 2] = str.length * 8;
	let a = 0x67452301;
	let b = 0xEFCDAB89;
	let c = 0x98BADCFE;
	let d = 0x10325476;

	for(i = 0; i < x.length; i += 16)
	{
		olda = a;
		oldb = b;
		oldc = c;
		oldd = d;

		let index = 0
		/*
		Soit [abcd k s i] notant l'opération
		a = b + ((a + F(b,c,d) + X[k] + T[i]) <<< s).
		*/
		let step_one_const = [7, 12, 17, 22]
		for (let o = 0; o < 4; o++)
		{
			a = step_one(a, b, c, d, x[i+ index], step_one_const[0], constantes[index++]);
			d = step_one(d, a, b, c, x[i+ index], step_one_const[1], constantes[index++]);
			c = step_one(c, d, a, b, x[i+ index], step_one_const[2], constantes[index++]);
			b = step_one(b, c, d, a, x[i+ index], step_one_const[3], constantes[index++]);
		}
		/*
		Soit [abcd k s i] l'opération
		a = b + ((a + G(b,c,d) + X[k] + T[i]) <<< s).
		*/
		let step_two_tab = [1, 6, 11, 0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12];
		let step_two_index = 0;
		let step_two_const = [5, 9, 14, 20]
		for (let o = 0; o < 4; o++)
		{
			a = step_two(a, b, c, d, x[i+ step_two_tab[step_two_index++]], 5, constantes[index++]);
			d = step_two(d, a, b, c, x[i+ step_two_tab[step_two_index++]], 9, constantes[index++]);
			c = step_two(c, d, a, b, x[i+ step_two_tab[step_two_index++]], 14, constantes[index++]);
			b = step_two(b, c, d, a, x[i+ step_two_tab[step_two_index++]], 20, constantes[index++]);
		}
		/*
		Soit [abcd k s t] l'opération
		a = b + ((a + H(b,c,d) + X[k] + T[i]) <<< s).
		*/
		let step_three_tab = [5, 8, 11, 14, 1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 15, 2];
		let step_three_index = 0;
		let step_three_const = [4, 11, 16, 23];
		for (let o = 0; o < 4; o++)
		{
			a = step_three(a, b, c, d, x[i+ step_three_tab[step_three_index++]], step_three_const[0], constantes[index++]);
			d = step_three(d, a, b, c, x[i+ step_three_tab[step_three_index++]], step_three_const[1], constantes[index++]);
			c = step_three(c, d, a, b, x[i+ step_three_tab[step_three_index++]], step_three_const[2], constantes[index++]);
			b = step_three(b, c, d, a, x[i+ step_three_tab[step_three_index++]], step_three_const[3], constantes[index++]);
		}
		/*
		Soit [abcd k s t] l'opération
		a = b + ((a + I(b,c,d) + X[k] + T[i]) <<< s).
		*/

		let step_four_tab = [0, 7, 14, 5, 12, 3, 10, 1, 8, 15, 6, 13, 4, 11, 2, 9];
		let step_four_index = 0;
		let step_four_const = [6, 10, 15, 21];
		for (let o = 0; o < 4; o++)
		{
			a = step_four(a, b, c, d, x[i+ step_four_tab[step_four_index++]], step_four_const[0], constantes[index++]);
			d = step_four(d, a, b, c, x[i+ step_four_tab[step_four_index++]], step_four_const[1] , constantes[index++]);
			c = step_four(c, d, a, b, x[i+ step_four_tab[step_four_index++]], step_four_const[2], constantes[index++]);
			b = step_four(b, c, d, a, x[i+ step_four_tab[step_four_index++]], step_four_const[3], constantes[index++]);
		}
		a += olda;
		b += oldb;
		c += oldc;
		d += oldd;
	}
	return number_to_hex(a) + number_to_hex(b) + number_to_hex(c) + number_to_hex(d);
}

console.log("Msg: '" + message + "'");
console.log(md5(message));

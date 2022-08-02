import { expect } from "chai";
import { countLetters, isPaired, treeToSentence, WordTree } from "../../src/part2/part2";

describe("Assignment 1 Part 2", () => {
    describe("countLetters", () => {
        it("counts letters", () => {
            expect(countLetters("aaabbbb")).to.deep.equal({"a": 3, "b":4});
            expect(countLetters("AaaBbbb")).to.deep.equal({"a": 3, "b":4});
            expect(countLetters("ABbbaab")).to.deep.equal({"a": 3, "b":4});
            expect(countLetters("I am robot")).to.deep.equal({"i": 1, "a": 1, "m": 1, "r":1, "o":2, "b":1, "t":1});
        });
    });

    describe("isPaired", () => {
        it("returns true for a string with paired parens", () => {
            expect(isPaired("([{}])")).to.be.true;
            expect(isPaired("This is ([some]) {text}.")).to.be.true;
            expect(isPaired("No parens, no problems.")).to.be.true;
            expect(isPaired("")).to.be.true;
        });

        it("returns false when the parens are not paired", () => {
            expect(isPaired("(]")).to.be.false;
            expect(isPaired("This is ]some[ }text{")).to.be.false;
            expect(isPaired("(")).to.be.false;
            expect(isPaired(")(")).to.be.false;
        });
    });

    describe("treeToSentence", () => {
        const t1: WordTree = {root:"hello", children:[{root: "world", children:[]}]}
        const t2: WordTree = {root:"hello", children:[{root: "there", children:[]}, {root:"!", children:[]}]}
        const t3: WordTree = {root:"hello", children:[{root: "there", children:[{root:"!", children:[]}]}]}
        it("Represents a tree as a sentence", () => {
            expect(treeToSentence(t1)).to.equal("hello world");
            expect(treeToSentence(t2)).to.equal("hello there !");
            expect(treeToSentence(t3)).to.equal("hello there !");

        });
    });
});


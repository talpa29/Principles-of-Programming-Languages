import * as R from "ramda";

const stringToArray = R.split("");

/* Question 1 */
export const countLetters =  (s: string) =>  {
    return R.reduce((acc,curr) => {
        if(acc[curr] != undefined) {
            acc[curr]++;
            return acc;
        }
        else {
            acc[curr] =  1;
            return acc;
        }
            
    }, Object.create({}), stringToArray(R.toLower(s)))
    
}



// /* Question 2 */
export const isPaired = (s: string): boolean => {
    return R.reduce((acc,curr) => {
        if(curr === ')' || curr === '}' || curr === ']') {
            switch (curr) {
                case ']' : {
                    if (acc.charAt(acc.length - 1) === '[') {
                        acc = acc.slice(0,acc.length - 1);
                        return acc;
                    }
                    else {
                        return acc + curr;
                    }
                }
                case '}' : {
                    if (acc.charAt(acc.length - 1) === '{') {
                        acc = acc.slice(0,acc.length - 1);
                        return acc;
                    }
                    else {
                        return acc + curr;
                    }
                }
                case ')' : {
                    if (acc.charAt(acc.length - 1) === '(') {
                        acc = acc.slice(0,acc.length - 1);
                        return acc;
                    }
                    else {
                        return acc + curr;
                    }
                }
                    
            }
        }
        else {
            return acc + curr;
        }
    }, "", R.filter(x => x === '(' || x === ')' || x === '{' || x === '}' || x === '[' || x === ']',  stringToArray(s))) === "";

}


/* Question 3 */
interface WordTree {
    root: string;
    children: WordTree[];
}

export const treeToSentence = (t: WordTree): string => t.root + R.reduce((acc,curr) => acc + " " + treeToSentence(curr) ,"",t.children);





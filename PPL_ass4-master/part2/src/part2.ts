export const MISSING_KEY = '___MISSING_KEY___'
export const MISSING_TABLE_SERVICE = '___MISSING_TABLE_SERVICE___'

export type Table<T> = Readonly<Record<string, Readonly<T>>>

export type TableService<T> = {
    get(key: string): Promise<T>;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
}

// Q 2.1 (a)
export function makeTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>): TableService<T> {
    return {
        get(key: string): Promise<T> {
            return sync().then(ta => {
                const x = ta[key]
                return new Promise<T>((resolve, reject) => {
                   typeof x !== 'undefined' && x !== null! ? resolve(x) : reject(MISSING_KEY);
               })
            })
        },
        set(key: string, val: T): Promise<void> {
            const table: Table<T> = {[key] : val} ;
            return sync().then((ta) => {
                  const newTable = Object.assign(ta,table);
                  sync(newTable).then(() => {return Promise.resolve()})
                  .catch(() => {return Promise.reject(MISSING_KEY)});
            })
                .catch(() => {return Promise.reject(MISSING_KEY)})
            
        },
        delete(key: string): Promise<void> {
            const t: Table<T> = {[key]: null!}
            return sync().then((ta) => {
                const newTable = Object.assign(ta,t);
                  sync(newTable).then(() => {return Promise.resolve()})
                  .catch(() => {return Promise.reject(MISSING_KEY)});
            })
                .catch(() => {return Promise.reject(MISSING_KEY)})
        }
    }
}

// Q 2.1 (b)
export function getAll<T>(store: TableService<T>, keys: string[]): Promise<T[]> {
    const promises = keys.map(key => store.get(key))
    return Promise.all(promises)
}


// Q 2.2
export type Reference = { table: string, key: string }

export type TableServiceTable = Table<TableService<object>>

export function isReference<T>(obj: T | Reference): obj is Reference {
    return typeof obj === 'object' && 'table' in obj
}

export async function constructObjectFromTables(tables: TableServiceTable, ref: Reference) {
    let ans = {}
    async function deref(ref: Reference) {
        if(!Object.keys(tables).includes(ref.table))
            return Promise.reject(MISSING_TABLE_SERVICE)
        for (const [key, value] of Object.entries(tables)) {
            if(key === ref.table){
                const matching_table = await tables[key].get(ref.key)
                if(matching_table === undefined)
                    return Promise.reject(MISSING_KEY)               
                for (const [k, value] of Object.entries(matching_table)) {  
                            if(isReference(value)) {
                                ref = value
                                const val = await constructObjectFromTables(tables,ref)
                                const toadd = {[k] : val}
                                ans = Object.assign(ans, toadd)
                            }
                            else {
                                ans = Object.assign(ans, {[k]:value})

                            } 
                }
                
                return ans
            }
        }
    }

    return deref(ref)
}

// Q 2.3

export function lazyProduct<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        for (const v of g1()) {
            for (const j of g2()) {
                yield [v,j]
            }
        }
    }
}

export function lazyZip<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    let t = g1()
    let a = g2()

    return function* () {
        let t1 = t.next()
        let a1 = a.next()
        while(!t1.done) {
            yield[t1.value,a1.value]
            t1 = t.next()
            a1 = a.next()
        }
        
    }
}

// Q 2.4
export type ReactiveTableService<T> = {
    get(key: string): T;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
    subscribe(observer: (table: Table<T>) => void): void
}

export async function makeReactiveTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>, optimistic: boolean): Promise<ReactiveTableService<T>> {
    const opt: boolean = optimistic
    let subscriber:(table: Table<T>) => void

    let _table: Table<T> = await sync()

    const handleMutation = async (newTable: Table<T>) => {
        if(optimistic) {
            try {
                if(Object.values(newTable).includes(null!)) {
                    let switch_table :Record<string, Readonly<T>> = {}
                    for(const [k, value] of Object.entries(_table)){
                        if(k !== Object.keys(newTable)[0]) {
                            switch_table[k] = value
                        }
                    }
                    subscriber(switch_table)
                    _table = await sync(switch_table)    
                }
                else {
                    let switch_table :Record<string, Readonly<T>> = {}
                    for(const [k, value] of Object.entries(_table)){
                        switch_table[k] = value
                    }
                    for(const [k, value] of Object.entries(newTable)){
                        switch_table[k] = value
                    }
                    subscriber(switch_table)
                    const to_replace = Object.assign(_table,switch_table);
                    _table = await sync(to_replace)
  
                }
            }
            catch {
                subscriber(_table)
                return Promise.reject('__EXPECTED_FAILURE__')
            }
        }
        else {
            if(Object.values(newTable).includes(null!)) {
                let switch_table :Record<string, Readonly<T>> = {}
                for(const [k, value] of Object.entries(_table)){
                    if(k !== Object.keys(newTable)[0]) {
                        switch_table[k] = value
                    }
                }
                _table = await sync(switch_table)
                subscriber(_table)
            }
            else {
                const to_replace = Object.assign(_table,newTable);
                _table = await sync(to_replace)
                subscriber(_table)
            }
        }

        // if (optimistic) {
        //     subscriber(newTable)
        //     try {
        //         _table = await sync(newTable)
        //     } 
        //     catch (err) {
        //         subscriber(_table)
        //         return Promise.reject(err)
        //     }
            
        // } 
        // else {
        //     _table = await sync(newTable)
        //     subscriber(_table)
        // }

    }
    return {
        get(key: string): T {
            if (key in _table) {
                return _table[key]
            } else {
                throw MISSING_KEY
            }
        },
        set(key: string, val: T): Promise<void> {
            const table: Table<T> = {[key] : val}
            return  handleMutation(table)
        },
        delete(key: string): Promise<void> {
            let tmp: Record<string, Readonly<T>> = {[key] : null!}
            return handleMutation(tmp)
        },

        subscribe(observer: (table: Table<T>) => void): void {
            subscriber = observer
        }
    }
}
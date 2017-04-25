/*
 * Copyright 2017 Magnus Madsen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ca.uwaterloo.flix.util.collection

import scala.collection.mutable

class MultiMap[K, V] {

  private val m = mutable.Map.empty[K, Set[V]]

  /**
    * Returns the set of values associated with the given key `k`.
    */
  def get(k: K): Set[V] = m.getOrElse(k, Set.empty)

  /**
    * Returns the keys of the multi map.
    */
  def keys: Set[K] = m.keySet.toSet

  /**
    * Returns the values of the multi map.
    */
  def values: Set[Set[V]] = m.values.toSet

  /**
    * Adds the value `v` to the set of values associated with the key `k`.
    */
  def put(k: K, v: V): Unit = m.get(k) match {
    case None => m.put(k, Set(v))
    case Some(vs) => m.put(k, vs + v)
  }

}